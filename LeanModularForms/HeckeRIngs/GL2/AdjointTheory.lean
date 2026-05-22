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
# Hecke adjoint theory and eigenform diagonalization

This file develops the adjoint theory of Hecke operators with respect to the
Petersson inner product, culminating in the existence of a simultaneous
eigenform basis for cusp form spaces.

## Main results

* `heckeT_p_adjoint` — T_p* = ⟨p⟩⁻¹ T_p (Diamond–Shurman Thm 5.5.3)
* `diamondOp_petersson_unitary` — `⟨d⟩` is unitary for pet
* `heckeT_n_petersson_normal` — T_n is normal
* `exists_simultaneous_eigenform_basis` — spectral theorem for Hecke operators

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

private noncomputable def adjointGamma0Rep (p N : ℕ) (hpN : Nat.Coprime p N) :
    ↥(Gamma0 N) :=
  let m := Int.gcdA p N
  let n := -(Int.gcdB p N)
  ⟨⟨!![(p : ℤ), n; (N : ℤ), m], by
      have hbez := Int.gcd_eq_gcd_ab p N
      rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
      simp only [Matrix.det_fin_two_of]
      linarith⟩, by
      rw [Gamma0_mem]; simp⟩

private lemma adjointGamma0Rep_units (p N : ℕ) (hpN : Nat.Coprime p N) [NeZero N] :
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

private lemma coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv
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

private lemma coe_diamondOp_cusp_eq_slash_sigma_p
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

private lemma slash_sigma_p_diamond_inv_cusp_eq
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

private noncomputable def adjointGamma1Rep (p N : ℕ) (hpN : Nat.Coprime p N) :
    SL(2, ℤ) :=
  let a := Int.gcdA p N
  let b := Int.gcdB p N
  ⟨!![(p : ℤ) * a, b; -(N : ℤ), 1], by
    have hbez := Int.gcd_eq_gcd_ab p N
    rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
    simp only [Matrix.det_fin_two_of]
    linarith⟩

private lemma adjointGamma1Rep_mem_Gamma1 (p N : ℕ) [NeZero N]
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

private lemma adjointGamma0Rep_mul_sigma_p_mem_Gamma1
    (p N : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have hbez := Int.gcd_eq_gcd_ab p N
  rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
  refine ⟨?_, ?_, ?_⟩
  ·
    show (((((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN).val 0 0 : ℤ) : ZMod N) = 1
    have h_mul : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
        sigma_p_specific N p hp hpN).val =
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val *
          (sigma_p_specific N p hp hpN).val := by
      rfl
    rw [h_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have h_γ₀_00 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 0 0 : ℤ)
        = (p : ℤ) := by
      simp [adjointGamma0Rep]
    have h_γ₀_01 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 0 1 : ℤ)
        = -(Int.gcdB p N) := by
      simp [adjointGamma0Rep]
    have h_σp_00 : ((sigma_p_specific N p hp hpN).val 0 0 : ℤ) =
        (aInvOfCoprime N p hpN : ℤ) := by
      simp [sigma_p_specific]
    have h_σp_10 : ((sigma_p_specific N p hp hpN).val 1 0 : ℤ) =
        (N : ℤ) * mIdxOfCoprime N p hpN := by
      simp [sigma_p_specific]
    rw [h_γ₀_00, h_γ₀_01, h_σp_00, h_σp_10]
    push_cast
    have h_ap : ((aInvOfCoprime N p hpN : ZMod N)) * (p : ZMod N) = 1 :=
      aInvOfCoprime_mul_eq_one N p hpN
    have h_N : (N : ZMod N) = 0 := ZMod.natCast_self N
    rw [show (-(Int.gcdB ↑p ↑N : ZMod N)) * ((N : ZMod N) * (mIdxOfCoprime N p hpN : ZMod N))
        = 0 by rw [h_N]; ring]
    rw [add_zero, mul_comm]
    exact h_ap
  ·
    show (((((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN).val 1 1 : ℤ) : ZMod N) = 1
    have h_mul : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
        sigma_p_specific N p hp hpN).val =
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val *
          (sigma_p_specific N p hp hpN).val := rfl
    rw [h_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have h_γ₀_10 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 1 0 : ℤ)
        = (N : ℤ) := by
      simp [adjointGamma0Rep]
    have h_γ₀_11 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 1 1 : ℤ)
        = Int.gcdA p N := by
      simp [adjointGamma0Rep]
    have h_σp_01 : ((sigma_p_specific N p hp hpN).val 0 1 : ℤ) = 1 := by
      simp [sigma_p_specific]
    have h_σp_11 : ((sigma_p_specific N p hp hpN).val 1 1 : ℤ) = (p : ℤ) := by
      simp [sigma_p_specific]
    rw [h_γ₀_10, h_γ₀_11, h_σp_01, h_σp_11]
    push_cast
    rw [show (((N : ZMod N)) * 1) = 0 by rw [ZMod.natCast_self]; ring]
    rw [zero_add]
    have h_bez_mod : ((Int.gcdA p N : ZMod N)) * (p : ZMod N) = 1 := by
      have := congr_arg (Int.cast : ℤ → ZMod N) hbez
      simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_self] at this
      linear_combination -this
    exact h_bez_mod
  ·
    show (((((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN).val 1 0 : ℤ) : ZMod N) = 0
    have h_mul : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
        sigma_p_specific N p hp hpN).val =
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val *
          (sigma_p_specific N p hp hpN).val := rfl
    rw [h_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have h_γ₀_10 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 1 0 : ℤ)
        = (N : ℤ) := by
      simp [adjointGamma0Rep]
    have h_γ₀_11 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 1 1 : ℤ)
        = Int.gcdA p N := by
      simp [adjointGamma0Rep]
    have h_σp_00 : ((sigma_p_specific N p hp hpN).val 0 0 : ℤ) =
        (aInvOfCoprime N p hpN : ℤ) := by
      simp [sigma_p_specific]
    have h_σp_10 : ((sigma_p_specific N p hp hpN).val 1 0 : ℤ) =
        (N : ℤ) * mIdxOfCoprime N p hpN := by
      simp [sigma_p_specific]
    rw [h_γ₀_10, h_γ₀_11, h_σp_00, h_σp_10]
    push_cast
    rw [show ((N : ZMod N)) * (aInvOfCoprime N p hpN : ZMod N) = 0 by
      rw [ZMod.natCast_self]; ring]
    rw [show ((Int.gcdA ↑p ↑N : ZMod N)) * ((N : ZMod N) * (mIdxOfCoprime N p hpN : ZMod N)) = 0 by
      rw [ZMod.natCast_self]; ring]
    ring

private noncomputable def gamma1_of_gamma0_sigma_p
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

private lemma sigma_p_inv_eq_gamma1_inv_mul_gamma0
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

private lemma peterssonAdj_mul (α β : GL (Fin 2) ℝ) :
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

private lemma peterssonAdj_inv_mapGL_SL_eq_self (q : SL(2, ℤ)) :
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

private lemma peterssonAdj_smul_eq (α : GL (Fin 2) ℝ) (τ : ℍ) :
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

private lemma peterssonInner_mapGL_smul_eq_slash
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

/-! ### T090 Hecke conjugate intersection group `Γ_p(α)`

Foundational infrastructure for the **aggregate full-Hecke-family swap**
`h_HeckeFD_swap` (DS Thm 5.5.3 sum-level Hecke adjoint).  As established in
prior T090 stints, the per-α individual SL-tile balance is mathematically
unsatisfiable: `(⟨p⟩⁻¹f) ∣ glMap M_∞` is invariant only under
`α⁻¹ Γ₁(N) α ∩ Γ₁(N) =: Γ_p(α)`, **not** under Γ₁(N).  The full DS Thm
5.5.3 route therefore necessarily passes through the conjugate
intersection group `Γ_p(α)` and its fundamental domain.

Mathlib provides `CongruenceSubgroup.conjGL` (`Mathlib.NumberTheory.ModularForms.CongruenceSubgroups`)
as the conjugate `α⁻¹ · Γ · α ∩ SL(2,ℤ)`, plus `IsCongruenceSubgroup.conjGL`
showing it is itself a congruence subgroup.  Combined with the standard
`Γ₁(N) ⊓ K` intersection, this gives the conjugate intersection group
`Γ_p(α) := Γ₁(N) ⊓ conjGL Γ₁(N) α`, the kernel of the right Hecke action
of α on the Γ₁(N)-coset space.

This subsection provides the minimal foundational infrastructure
(definition + finite-index + congruence-subgroup-ness) needed downstream
for fundamental-domain transport between Γ₁(N)-FD and α • Γ_p(α)-FD
(the geometric content underlying `h_HeckeFD_swap`). -/

open CongruenceSubgroup Pointwise ConjAct in
/-- **T090 Hecke conjugate intersection group `Γ_p(α)`.** -/
noncomputable def Gamma_p_α (α : GL (Fin 2) ℚ) : Subgroup SL(2, ℤ) :=
  conjGL (Gamma1 N) (α.map (Rat.castHom ℝ)) ⊓ Gamma1 N

open CongruenceSubgroup Pointwise ConjAct in
/-- **T090 `Γ_p(α)` has finite index in `SL(2, ℤ)`.** -/
theorem Gamma_p_α_finiteIndex (α : GL (Fin 2) ℚ) :
    (Gamma_p_α (N := N) α).FiniteIndex := by
  show (conjGL (Gamma1 N) (α.map (Rat.castHom ℝ)) ⊓ Gamma1 N).FiniteIndex
  haveI : (conjGL (Gamma1 N) (α.map (Rat.castHom ℝ))).FiniteIndex :=
    ((Gamma1_is_congruence N).conjGL α).finiteIndex
  exact inferInstance

open CongruenceSubgroup Pointwise ConjAct in
/-- **T090 `Γ_p(α) ≤ Γ₁(N)`.**

Trivial right-inf inclusion: by definition `Gamma_p_α α := conjGL Γ₁(N) α ⊓ Γ₁(N)`,
so `Gamma_p_α α ≤ Γ₁(N)` is `inf_le_right`. -/
lemma Gamma_p_α_le_Gamma1 (α : GL (Fin 2) ℚ) :
    Gamma_p_α (N := N) α ≤ Gamma1 N :=
  inf_le_right

open CongruenceSubgroup Pointwise ConjAct in
/-- **T090 `Γ_p(α)` has finite index in `Γ₁(N)`.** -/
theorem Gamma_p_α_finiteIndex_in_Gamma1 (α : GL (Fin 2) ℚ) :
    ((Gamma_p_α (N := N) α).subgroupOf (Gamma1 N)).FiniteIndex := by
  haveI : (Gamma_p_α (N := N) α).FiniteIndex := Gamma_p_α_finiteIndex α
  exact Subgroup.instFiniteIndex_subgroupOf _ _

open CongruenceSubgroup Pointwise ConjAct in
/-- **T090 `Γ_p(α)` conjugation embedding.** -/
lemma Gamma_p_α_conj_mem_Gamma1 (α : GL (Fin 2) ℚ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) α) :
    ∃ δ ∈ Gamma1 N,
      ((mapGL ℝ δ : GL (Fin 2) ℝ)) =
        (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
          (mapGL ℝ γ : GL (Fin 2) ℝ) *
          ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ := by
  rcases hγ with ⟨h_conj, _⟩
  rcases mem_conjGL.mp h_conj with ⟨δ, hδ_mem, hδ_eq⟩
  exact ⟨δ, hδ_mem, hδ_eq⟩

open CongruenceSubgroup Pointwise ConjAct in
/-- **T090 conjGL ↔ ConjAct.toConjAct GL-level identity.** -/
lemma conjGL_map_eq_conjAct_inv_smul_inter
    (Γ : Subgroup SL(2, ℤ)) (g : GL (Fin 2) ℝ) :
    (conjGL Γ g).map (mapGL ℝ) =
      (ConjAct.toConjAct g⁻¹ • (Γ.map (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ))) ⊓
        (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range := by
  rw [conjGL, Subgroup.map_comap_eq, inf_comm]

open CongruenceSubgroup Pointwise ConjAct in
/-- **T090 conjugation-by-α function `Γ_p(α) → Γ₁(N)`.** -/
noncomputable def Gamma_p_α_conjBy (α : GL (Fin 2) ℚ)
    (γ : Gamma_p_α (N := N) α) : Gamma1 N :=
  ⟨Classical.choose (Gamma_p_α_conj_mem_Gamma1 α γ.property),
    (Classical.choose_spec (Gamma_p_α_conj_mem_Gamma1 α γ.property)).1⟩

open CongruenceSubgroup Pointwise ConjAct in
/-- **T090 defining equality of `Gamma_p_α_conjBy`.**

`mapGL ℝ (Gamma_p_α_conjBy α γ : SL(2, ℤ)) = α · mapGL ℝ γ · α⁻¹`
in `GL (Fin 2) ℝ`. -/
lemma Gamma_p_α_conjBy_spec (α : GL (Fin 2) ℚ)
    (γ : Gamma_p_α (N := N) α) :
    (mapGL ℝ ((Gamma_p_α_conjBy α γ : SL(2, ℤ))) : GL (Fin 2) ℝ) =
      (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ ((γ : SL(2, ℤ))) : GL (Fin 2) ℝ) *
        ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ :=
  (Classical.choose_spec (Gamma_p_α_conj_mem_Gamma1 α γ.property)).2

open CongruenceSubgroup Pointwise ConjAct in
/-- **T090 injectivity of `Gamma_p_α_conjBy`.** -/
lemma Gamma_p_α_conjBy_injective (α : GL (Fin 2) ℚ) :
    Function.Injective (Gamma_p_α_conjBy (N := N) α) := by
  intro γ₁ γ₂ h
  apply Subtype.ext
  have h_mapGL :
      (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ ((γ₁ : SL(2, ℤ))) : GL (Fin 2) ℝ) *
        ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ =
      (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ ((γ₂ : SL(2, ℤ))) : GL (Fin 2) ℝ) *
        ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ := by
    have hh : (Gamma_p_α_conjBy α γ₁ : SL(2, ℤ)) =
        (Gamma_p_α_conjBy α γ₂ : SL(2, ℤ)) := congrArg Subtype.val h
    have h1 := Gamma_p_α_conjBy_spec α γ₁
    have h2 := Gamma_p_α_conjBy_spec α γ₂
    rw [← h1, hh, h2]
  have h_γ : (mapGL ℝ ((γ₁ : SL(2, ℤ))) : GL (Fin 2) ℝ) =
      mapGL ℝ ((γ₂ : SL(2, ℤ))) := by
    have h_step1 : (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ ((γ₁ : SL(2, ℤ))) : GL (Fin 2) ℝ) =
        (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) * mapGL ℝ ((γ₂ : SL(2, ℤ))) := by
      have hh1 := congrArg (· * (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) h_mapGL
      simp only [inv_mul_cancel_right] at hh1
      exact hh1
    exact mul_left_cancel h_step1
  exact mapGL_injective h_γ

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **T090 downstream bridge: slash by α is `Γ_p(α)`-invariant on Γ₁(N)-cusp forms.** -/
lemma slash_α_Gamma_p_α_invariant (α : GL (Fin 2) ℚ)
    (f : ℍ → ℂ)
    (hf : ∀ δ ∈ Gamma1 N,
      f ∣[k] ((mapGL ℝ δ : GL (Fin 2) ℝ)) = f)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) α) :
    (f ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))) ∣[k]
      ((mapGL ℝ γ : GL (Fin 2) ℝ)) =
    f ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) := by
  obtain ⟨δ, hδ_mem, hδ_eq⟩ := Gamma_p_α_conj_mem_Gamma1 α hγ
  have hαγ : (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
      (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ δ : GL (Fin 2) ℝ) * (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) := by
    rw [hδ_eq]; group
  rw [← SlashAction.slash_mul, hαγ, SlashAction.slash_mul, hf δ hδ_mem]

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **T090 cusp-form specialization of `slash_α_Gamma_p_α_invariant`.** -/
lemma slash_α_Gamma_p_α_invariant_cuspForm
    (α : GL (Fin 2) ℚ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) α) :
    ((⇑f) ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))) ∣[k]
      ((mapGL ℝ γ : GL (Fin 2) ℝ)) =
    (⇑f) ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) := by
  refine slash_α_Gamma_p_α_invariant α (⇑f) ?_ hγ
  intro δ hδ
  rw [show ((mapGL ℝ δ : GL (Fin 2) ℝ)) =
        (((δ : SL(2, ℤ)) : GL (Fin 2) ℝ)) from rfl, ← ModularForm.SL_slash]
  exact slash_Gamma1_eq f δ hδ

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **T090 finite-index FD-transport reduction (statement-level).** -/
lemma slash_α_Gamma_p_α_invariant_at_FD_decomp_witness
    (α : GL (Fin 2) ℚ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∀ {γ : SL(2, ℤ)}, γ ∈ Gamma_p_α (N := N) α →
      ((⇑f) ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))) ∣[k]
        ((mapGL ℝ γ : GL (Fin 2) ℝ)) =
      (⇑f) ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) :=
  fun {γ} hγ ↦ slash_α_Gamma_p_α_invariant_cuspForm α f hγ

/-! ### T090 FD transport adapters -/

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **T090 / T106 FD-shift adapter (generic GL(2, ℝ)⁺ form)**. -/
theorem isFundamentalDomain_GLPos_smul_conjAct
    (α' : GL(2, ℝ)⁺) {H₁ : Subgroup (GL(2, ℝ)⁺)} {s : Set ℍ}
    (hs : MeasureTheory.IsFundamentalDomain (H₁ : Subgroup (GL(2, ℝ)⁺)) s μ_hyp) :
    MeasureTheory.IsFundamentalDomain
      ((ConjAct.toConjAct α' • H₁ : Subgroup (GL(2, ℝ)⁺)))
      (α' • s) μ_hyp :=
  MeasureTheory.IsFundamentalDomain.smul_of_eq_conjAct hs rfl

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **T090 / T106 FD-shift adapter for `Γ_p(α)` (GL(2, ℝ)⁺ lift,
conditional input hypothesis)**. -/
theorem Gamma_p_α_GLPos_lift_FD_smul_conjAct
    (α : GL (Fin 2) ℚ) (α' : GL(2, ℝ)⁺) {s : Set ℍ}
    (hs : IsFundamentalDomain
      ((Gamma_p_α (N := N) α).map
        (ModularGroup.coeHom : SL(2, ℤ) →* GL(2, ℝ)⁺))
      s μ_hyp) :
    IsFundamentalDomain
      (ConjAct.toConjAct α' •
        ((Gamma_p_α (N := N) α).map
          (ModularGroup.coeHom : SL(2, ℤ) →* GL(2, ℝ)⁺)) :
          Subgroup GL(2, ℝ)⁺)
      (α' • s) μ_hyp :=
  isFundamentalDomain_GLPos_smul_conjAct α' hs

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **T090 / T106 finite-index FD decomposition for `Γ_p(α) ≤ Γ₁(N)`
(conditional ambient form)**. -/
theorem Gamma_p_α_FD_finite_index_decomp
    {G_outer : Type*} [Group G_outer] [MulAction G_outer ℍ]
    [MeasurableConstSMul G_outer ℍ] [SMulInvariantMeasure G_outer ℍ μ_hyp]
    (α : GL (Fin 2) ℚ) (φ : SL(2, ℤ) →* G_outer) {D : Set ℍ}
    (hD : IsFundamentalDomain ((Gamma1 N).map φ) D μ_hyp)
    [Countable
      (((Gamma1 N).map φ) ⧸
        (((Gamma_p_α (N := N) α).map φ).subgroupOf ((Gamma1 N).map φ)))] :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) α).map φ).subgroupOf ((Gamma1 N).map φ))
      (⋃ q : ((Gamma1 N).map φ) ⧸
              (((Gamma_p_α (N := N) α).map φ).subgroupOf ((Gamma1 N).map φ)),
        ((q.out : ((Gamma1 N).map φ)) : G_outer)⁻¹ • D)
      μ_hyp :=
  hD.subgroup_iUnion_out_smul _

/-! ### Phase D: PSL(2, ℝ) ambient instantiations of the FD-shift adapters

We re-instantiate the generic GL(2, ℝ)⁺ adapters from above at the
projective real ambient `PSL(2, ℝ)`, using the Phase A–C foundation
(`MulAction PSL(2, ℝ) ℍ`, `instSMulInvMeasure_PSL_R`, `SL2Z_to_PSL2R`,
`isFundamentalDomain_Gamma1_PSL_R`, `GLPos_to_PSL_R_term`).  Unlike the
`GL(2, ℝ)⁺`-subgroup version, the projective ambient hosts a satisfiable
input FD for *any* `[NeZero N]` (no `±I`-kernel obstruction), and the
`α'`-shift uses the term-level projective representative
`GLPos_to_PSL_R_term α' : PSL(2, ℝ)`. -/

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **Phase D step 2 — generic projective FD-shift adapter at PSL(2, ℝ)**. -/
theorem isFundamentalDomain_PSL_R_smul_conjAct
    (α : PSL(2, ℝ)) {H₁ : Subgroup (PSL(2, ℝ))} {s : Set ℍ}
    (hs : MeasureTheory.IsFundamentalDomain (H₁ : Subgroup (PSL(2, ℝ))) s μ_hyp) :
    MeasureTheory.IsFundamentalDomain
      ((ConjAct.toConjAct α • H₁ : Subgroup (PSL(2, ℝ))))
      (α • s) μ_hyp :=
  MeasureTheory.IsFundamentalDomain.smul_of_eq_conjAct hs rfl

open CongruenceSubgroup in
/-- **Phase E1 — finite-index instance for the projective image of `Γ_p(α)`
inside the projective image of `Γ₁(N)`.** -/
instance Gamma_p_α_image_PSL_R_finiteIndex_in_Gamma1_image
    (α : GL (Fin 2) ℚ) :
    (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
      ((Gamma1 N).map SL2Z_to_PSL2R)).FiniteIndex := by
  haveI : (Gamma_p_α (N := N) α).FiniteIndex := Gamma_p_α_finiteIndex α
  haveI : (Gamma_p_α (N := N) α ⊔ SL2Z_to_PSL2R.ker).FiniteIndex :=
    Subgroup.finiteIndex_of_le le_sup_left
  refine ⟨?_⟩
  show ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).relIndex
        ((Gamma1 N).map SL2Z_to_PSL2R) ≠ 0
  rw [Subgroup.relIndex_map_map]
  exact (Subgroup.instFiniteIndex_subgroupOf
    (Gamma1 N ⊔ SL2Z_to_PSL2R.ker)
    (H := Gamma_p_α (N := N) α ⊔ SL2Z_to_PSL2R.ker)).index_ne_zero

open CongruenceSubgroup in
/-- **Phase E1 (companion) — `Fintype` of the right-coset space.** -/
noncomputable instance Gamma_p_α_image_PSL_R_quotient_fintype
    (α : GL (Fin 2) ℚ) :
    Fintype
      (((Gamma1 N).map SL2Z_to_PSL2R) ⧸
        (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
          ((Gamma1 N).map SL2Z_to_PSL2R))) :=
  Subgroup.fintypeQuotientOfFiniteIndex

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase D step 3 — finite-index FD decomposition for `Γ_p(α) ≤ Γ₁(N)`
at the PSL(2, ℝ) ambient.** -/
theorem Gamma_p_α_PSL_R_FD_finite_index_decomp
    (α : GL (Fin 2) ℚ)
    [Countable
      (((Gamma1 N).map SL2Z_to_PSL2R) ⧸
        (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
          ((Gamma1 N).map SL2Z_to_PSL2R)))] :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
        ((Gamma1 N).map SL2Z_to_PSL2R))
      (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
        ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
          Gamma1_fundDomain_PSL N)
      μ_hyp := by
  apply Gamma_p_α_FD_finite_index_decomp α SL2Z_to_PSL2R
  rw [map_SL2Z_to_PSL2R_eq_imageGamma1_PSL_R]
  exact isFundamentalDomain_Gamma1_PSL_R

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase E2 — `_auto` wrapper for the PSL(2, ℝ) FD decomposition.** -/
theorem Gamma_p_α_PSL_R_FD_finite_index_decomp_auto
    (α : GL (Fin 2) ℚ) :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
        ((Gamma1 N).map SL2Z_to_PSL2R))
      (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
        ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
          Gamma1_fundDomain_PSL N)
      μ_hyp :=
  Gamma_p_α_PSL_R_FD_finite_index_decomp α

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **Phase D step 4 — projective FD-shift adapter for `Γ_p(α)` at PSL(2, ℝ)**. -/
theorem Gamma_p_α_PSL_R_lift_FD_smul_conjAct
    (α : GL (Fin 2) ℚ) (α' : GL(2, ℝ)⁺) {s : Set ℍ}
    (hs : IsFundamentalDomain
      ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) s μ_hyp) :
    IsFundamentalDomain
      ((ConjAct.toConjAct (GLPos_to_PSL_R_term α') •
        ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)) :
          Subgroup (PSL(2, ℝ)))
      (GLPos_to_PSL_R_term α' • s) μ_hyp :=
  isFundamentalDomain_PSL_R_smul_conjAct (GLPos_to_PSL_R_term α') hs

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **Phase G — projective shifted FD-decomposition (general α/α').** -/
theorem Gamma_p_α_PSL_R_FD_finite_index_decomp_shifted
    (α : GL (Fin 2) ℚ) (α' : GL(2, ℝ)⁺) :
    IsFundamentalDomain
      ((ConjAct.toConjAct (GLPos_to_PSL_R_term α') •
        ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)) :
          Subgroup PSL(2, ℝ))
      (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
        (GLPos_to_PSL_R_term α' *
          ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
            (Gamma1_fundDomain_PSL N : Set ℍ))
      μ_hyp := by
  have h_subgroupOf := Gamma_p_α_PSL_R_FD_finite_index_decomp_auto (N := N) α
  have h_le : ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) ≤
              ((Gamma1 N).map SL2Z_to_PSL2R) :=
    Subgroup.map_mono (Gamma_p_α_le_Gamma1 α)
  have h_ambient :
      IsFundamentalDomain ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)
        (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
                (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                  ((Gamma1 N).map SL2Z_to_PSL2R)),
          ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
            (Gamma1_fundDomain_PSL N : Set ℍ))
        μ_hyp := by
    have h_image := h_subgroupOf.image_of_equiv (Equiv.refl ℍ)
      (MeasureTheory.Measure.QuasiMeasurePreserving.id _)
      ((Subgroup.subgroupOfEquivOfLe h_le).symm.toEquiv)
      (fun _ _ ↦ rfl)
    simp only [Equiv.coe_refl, Set.image_id] at h_image
    exact h_image
  have h_shifted := Gamma_p_α_PSL_R_lift_FD_smul_conjAct α α' h_ambient
  have h_set_eq :
      (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
        (GLPos_to_PSL_R_term α' *
          ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
            (Gamma1_fundDomain_PSL N : Set ℍ)) =
      GLPos_to_PSL_R_term α' •
        (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
                (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                  ((Gamma1 N).map SL2Z_to_PSL2R)),
          ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
            (Gamma1_fundDomain_PSL N : Set ℍ)) := by
    rw [Set.smul_set_iUnion]
    refine Set.iUnion_congr ?_
    intro q
    exact mul_smul _ _ _
  rw [h_set_eq]
  exact h_shifted

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase H — packaged per-α `Γ_p(α)`-fundamental-domain set.** -/
noncomputable def Gamma_p_α_fundDomain_PSL (α : GL (Fin 2) ℚ) : Set ℍ :=
  ⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
          (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
            ((Gamma1 N).map SL2Z_to_PSL2R)),
    ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
      (Gamma1_fundDomain_PSL N : Set ℍ)

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase H — Phase G shifted FD set as `α' • Γ_p(α)-FD` (generic).** -/
theorem Gamma_p_α_PSL_R_FD_finite_index_decomp_shifted_eq_smul
    (α : GL (Fin 2) ℚ) (α' : GL(2, ℝ)⁺) :
    (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
            (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
              ((Gamma1 N).map SL2Z_to_PSL2R)),
      (GLPos_to_PSL_R_term α' *
        ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) =
    GLPos_to_PSL_R_term α' • Gamma_p_α_fundDomain_PSL (N := N) α := by
  unfold Gamma_p_α_fundDomain_PSL
  rw [Set.smul_set_iUnion]
  exact Set.iUnion_congr fun q ↦ mul_smul _ _ _

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase J — generic SL outer-quotient ↔ scaled `Gamma1_fundDomain_PSL`
integral bridge.** -/
theorem setIntegral_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum
    (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ)
    (h_int : IntegrableOn h (Gamma1_fundDomain_PSL N) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
    (slToPslQuot_fiberCard N) • ∫ τ in Gamma1_fundDomain_PSL N, h τ ∂μ_hyp := by
  classical
  calc ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_fd_eq_fdo h q
    _ = ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        sum_SL_tile_eq_fiberwise_PSL_tile h h_inv
    _ = (slToPslQuot_fiberCard N) • ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
          ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        congr 1
        convert slToPslQuot_fiberCard_eq q' using 2
        congr
    _ = (slToPslQuot_fiberCard N) • ∫ τ in Gamma1_fundDomain_PSL N, h τ ∂μ_hyp := by
        rw [← setIntegral_Gamma1_fundDomain_PSL_eq_sum h h_int]

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase K — Petersson-integrand specialization of the Phase J generic
SL outer-quotient bridge.** -/
theorem peterssonInner_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
        petersson k ⇑f ⇑g τ ∂μ_hyp =
    (slToPslQuot_fiberCard N) •
      ∫ τ in Gamma1_fundDomain_PSL N, petersson k ⇑f ⇑g τ ∂μ_hyp :=
  setIntegral_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum
    (petersson k ⇑f ⇑g)
    (fun γ hγ τ ↦ petersson_Gamma1_invariant f g γ hγ τ)
    (integrableOn_petersson_Gamma1_fundDomain_PSL f g)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase L (a) — generic per-`q` SL slash-domain reducer.** -/
theorem peterssonInner_fd_slash_q_eq_setIntegral_shifted_fd
    (F G : ℍ → ℂ) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    peterssonInner k fd (F ∣[k] (q.out : SL(2, ℤ))⁻¹) (G ∣[k] (q.out : SL(2, ℤ))⁻¹) =
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
      petersson k F G τ ∂μ_hyp := by
  simp only [peterssonInner]
  simp_rw [petersson_slash_SL]
  rw [← Set.image_smul,
    ← (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase L (b) — DS-LHS branch per-`q` slash-compose + slash-domain reducer.** -/
theorem peterssonInner_slash_compose_q_eq_setIntegral_shifted_fd
    (A B : GL (Fin 2) ℝ) (q : SL(2, ℤ) ⧸ Gamma1 N) (F G : ℍ → ℂ) :
    peterssonInner k fd
      (F ∣[k] (A * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹)))
      (G ∣[k] (B * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹))) =
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
      petersson k (F ∣[k] A) (G ∣[k] B) τ ∂μ_hyp := by
  rw [SlashAction.slash_mul, SlashAction.slash_mul]
  exact peterssonInner_fd_slash_q_eq_setIntegral_shifted_fd
    (F ∣[k] A) (G ∣[k] B) q

open CongruenceSubgroup ModularGroup MeasureTheory in
/-- **Phase M (a) — image of `Γ_p(α)` in `PSL(2, ℤ)`.**

Direct PSL projection of `Γ_p(α) ≤ SL(2, ℤ)` via the canonical
`SL(2, ℤ) →* PSL(2, ℤ) = SL(2, ℤ) / {±I}`.  Mirrors `imageGamma1_PSL`
(`PeterssonLevelN.lean:508`) at the Γ_p(α) subgroup. -/
noncomputable def image_Gamma_p_α_PSL (α : GL (Fin 2) ℚ) : Subgroup PSL(2, ℤ) :=
  (Gamma_p_α (N := N) α).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

open CongruenceSubgroup in
/-- **Phase M (a) — `image_Gamma_p_α_PSL α` has finite index in `PSL(2, ℤ)`.**

The image of a finite-index subgroup under a surjective hom has finite index;
applied to the surjection `SL(2, ℤ) →* PSL(2, ℤ)` and the finite-index witness
`Gamma_p_α_finiteIndex`. -/
instance image_Gamma_p_α_PSL_finiteIndex (α : GL (Fin 2) ℚ) :
    (image_Gamma_p_α_PSL (N := N) α).FiniteIndex := by
  haveI : (Gamma_p_α (N := N) α).FiniteIndex :=
    Gamma_p_α_finiteIndex (N := N) α
  refine ⟨fun h ↦ ?_⟩
  have h_dvd : (image_Gamma_p_α_PSL (N := N) α).index ∣
      (Gamma_p_α (N := N) α).index := by
    apply Subgroup.index_map_dvd
    exact QuotientGroup.mk_surjective
  rw [h] at h_dvd
  exact Subgroup.FiniteIndex.index_ne_zero (Nat.eq_zero_of_zero_dvd h_dvd)

open CongruenceSubgroup in
/-- **Phase M (a) — `Fintype` of the right-coset space `PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL α`.**

Direct `Subgroup.fintypeQuotientOfFiniteIndex` from the FiniteIndex instance
above.  Used downstream by `Gamma_p_α_fundDomain_PSL_canonical` and any
finite-sum identity over PSL/image cosets. -/
noncomputable instance image_Gamma_p_α_PSL_quotient_fintype (α : GL (Fin 2) ℚ) :
    Fintype (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :=
  Subgroup.fintypeQuotientOfFiniteIndex

open CongruenceSubgroup in
/-- **Phase M (b) — `Fintype` of `SL(2, ℤ) ⧸ Γ_p(α)`.**

Required by `Finset.univ` in the fiber-cardinality and SL→PSL reindex
identities below.  Direct `Subgroup.fintypeQuotientOfFiniteIndex` on the
`Gamma_p_α_finiteIndex` witness. -/
noncomputable instance Gamma_p_α_quotient_fintype (α : GL (Fin 2) ℚ) :
    Fintype (SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) := by
  haveI : (Gamma_p_α (N := N) α).FiniteIndex :=
    Gamma_p_α_finiteIndex (N := N) α
  exact Subgroup.fintypeQuotientOfFiniteIndex

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (a) — canonical PSL-coset fundamental domain for `image_Gamma_p_α_PSL α`.** -/
noncomputable def Gamma_p_α_fundDomain_PSL_canonical (α : GL (Fin 2) ℚ) : Set ℍ :=
  ⋃ q : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
    ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ)

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (a) — `Gamma_p_α_fundDomain_PSL_canonical α` is a fundamental domain
for `image_Gamma_p_α_PSL α` acting on `ℍ`.** -/
theorem isFundamentalDomain_Gamma_p_α_PSL_canonical (α : GL (Fin 2) ℚ) :
    MeasureTheory.IsFundamentalDomain (image_Gamma_p_α_PSL (N := N) α)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp :=
  isFundamentalDomain_fdo_PSL.subgroup_iUnion_out_smul
    (image_Gamma_p_α_PSL (N := N) α)

open CongruenceSubgroup in
/-- **Phase M (b) — natural quotient map `SL ⧸ Γ_p(α) → PSL ⧸ image_Γ_p(α)_PSL`.**

Mirror of `slToPslQuot` (`PeterssonLevelN.lean:811`) at the Γ_p(α) subgroup.
Sends each `Γ_p(α)`-coset `[g]` to its `image_Gamma_p_α_PSL`-coset
`[PSL.mk g]`.  Well-defined by the inclusion `Γ_p(α).map (PSL.mk') ⊆ image_Γ_p(α)_PSL`. -/
noncomputable def slToPslQuot_Gamma_p_α (α : GL (Fin 2) ℚ) :
    SL(2, ℤ) ⧸ Gamma_p_α (N := N) α →
      PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α :=
  Quotient.lift
    (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply (QuotientGroup.eq).mpr
      have h_psl : (QuotientGroup.mk a : PSL(2, ℤ))⁻¹ * QuotientGroup.mk b =
          QuotientGroup.mk (a⁻¹ * b) := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rw [h_psl]
      exact ⟨a⁻¹ * b, hab, rfl⟩)

@[simp]
theorem slToPslQuot_Gamma_p_α_mk (α : GL (Fin 2) ℚ) (g : SL(2, ℤ)) :
    slToPslQuot_Gamma_p_α (N := N) α
        (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
      QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :=
  rfl

theorem slToPslQuot_Gamma_p_α_surjective (α : GL (Fin 2) ℚ) :
    Function.Surjective (slToPslQuot_Gamma_p_α (N := N) α) := by
  intro q'
  obtain ⟨g_psl, hg_psl⟩ := QuotientGroup.mk_surjective q'
  obtain ⟨g_sl, hg_sl⟩ := QuotientGroup.mk_surjective g_psl
  refine ⟨QuotientGroup.mk g_sl, ?_⟩
  rw [slToPslQuot_Gamma_p_α_mk, hg_sl, hg_psl]

open CongruenceSubgroup in
/-- **Phase M (b) — left-multiplication action on `SL ⧸ Γ_p(α)`.** -/
noncomputable def slLeftMul_Gamma_p_α (α : GL (Fin 2) ℚ) (h : SL(2, ℤ)) :
    SL(2, ℤ) ⧸ Gamma_p_α (N := N) α → SL(2, ℤ) ⧸ Gamma_p_α (N := N) α :=
  Quotient.lift (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk (h * g) : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply QuotientGroup.eq.mpr
      have : (h * a)⁻¹ * (h * b) = a⁻¹ * b := by group
      rw [this]; exact hab)

@[simp]
theorem slLeftMul_Gamma_p_α_mk (α : GL (Fin 2) ℚ) (h g : SL(2, ℤ)) :
    slLeftMul_Gamma_p_α (N := N) α h
        (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
      QuotientGroup.mk (h * g) :=
  rfl

theorem slLeftMul_Gamma_p_α_one (α : GL (Fin 2) ℚ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    slLeftMul_Gamma_p_α (N := N) α 1 q = q := by
  induction q using QuotientGroup.induction_on with | _ g => simp

theorem slLeftMul_Gamma_p_α_comp (α : GL (Fin 2) ℚ) (h₁ h₂ : SL(2, ℤ))
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    slLeftMul_Gamma_p_α (N := N) α h₁ (slLeftMul_Gamma_p_α (N := N) α h₂ q) =
      slLeftMul_Gamma_p_α (N := N) α (h₁ * h₂) q := by
  induction q using QuotientGroup.induction_on with | _ g => simp [mul_assoc]

open CongruenceSubgroup Classical in
/-- **Phase M (b) — uniform fiber size of `slToPslQuot_Gamma_p_α`.** -/
theorem slToPslQuot_Gamma_p_α_fiber_card_uniform (α : GL (Fin 2) ℚ)
    (q₁' q₂' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :
    haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
        slToPslQuot_Gamma_p_α (N := N) α q = q₁')).card =
      (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
        slToPslQuot_Gamma_p_α (N := N) α q = q₂')).card := by
  haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
  obtain ⟨q₁, hq₁⟩ := slToPslQuot_Gamma_p_α_surjective (N := N) α q₁'
  obtain ⟨q₂, hq₂⟩ := slToPslQuot_Gamma_p_α_surjective (N := N) α q₂'
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  set h := g₂ * g₁⁻¹ with hh_def
  refine Finset.card_bij'
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h q)
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h⁻¹ q)
    (fun q hq ↦ ?_)
    (fun q hq ↦ ?_)
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h⁻¹
        (slLeftMul_Gamma_p_α (N := N) α h q) = q
      rw [slLeftMul_Gamma_p_α_comp, inv_mul_cancel, slLeftMul_Gamma_p_α_one])
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h
        (slLeftMul_Gamma_p_α (N := N) α h⁻¹ q) = q
      rw [slLeftMul_Gamma_p_α_comp, mul_inv_cancel, slLeftMul_Gamma_p_α_one])
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk (h * g)) = q₂'
    rw [slToPslQuot_Gamma_p_α_mk]
    have hq_psl : (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) = q₁' := hq
    have h_psl : (QuotientGroup.mk (h * g) : PSL(2, ℤ)) =
        (QuotientGroup.mk h : PSL(2, ℤ)) * (QuotientGroup.mk g : PSL(2, ℤ)) :=
      (QuotientGroup.mk_mul _ _ _).symm
    rw [h_psl]
    have h_h_psl : (QuotientGroup.mk h : PSL(2, ℤ)) =
        QuotientGroup.mk g₂ * (QuotientGroup.mk g₁)⁻¹ := by
      rw [hh_def, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rw [h_h_psl]
    have hq_eq_g₁ : (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) =
        QuotientGroup.mk (QuotientGroup.mk g₁ : PSL(2, ℤ)) := by
      rw [hq_psl]; exact hq₁.symm
    rw [QuotientGroup.eq] at hq_eq_g₁
    rw [show q₂' = QuotientGroup.mk (QuotientGroup.mk g₂ : PSL(2, ℤ)) from hq₂.symm,
      QuotientGroup.eq]
    have : (QuotientGroup.mk g₂ * (QuotientGroup.mk g₁)⁻¹ *
          (QuotientGroup.mk g : PSL(2, ℤ)))⁻¹ * QuotientGroup.mk g₂ =
        (QuotientGroup.mk g : PSL(2, ℤ))⁻¹ * QuotientGroup.mk g₁ := by group
    rw [this]; exact hq_eq_g₁
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk (h⁻¹ * g)) = q₁'
    rw [slToPslQuot_Gamma_p_α_mk]
    have hq_psl : (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) = q₂' := hq
    have h_psl : (QuotientGroup.mk (h⁻¹ * g) : PSL(2, ℤ)) =
        (QuotientGroup.mk h : PSL(2, ℤ))⁻¹ * (QuotientGroup.mk g : PSL(2, ℤ)) := by
      rw [show (h⁻¹ * g : SL(2, ℤ)) = h⁻¹ * g from rfl,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rw [h_psl]
    have h_h_psl : (QuotientGroup.mk h : PSL(2, ℤ)) =
        QuotientGroup.mk g₂ * (QuotientGroup.mk g₁)⁻¹ := by
      rw [hh_def, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rw [h_h_psl]
    have hq_eq_g₂ : (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) =
        QuotientGroup.mk (QuotientGroup.mk g₂ : PSL(2, ℤ)) := by
      rw [hq_psl]; exact hq₂.symm
    rw [QuotientGroup.eq] at hq_eq_g₂
    rw [show q₁' = QuotientGroup.mk (QuotientGroup.mk g₁ : PSL(2, ℤ)) from hq₁.symm,
      QuotientGroup.eq]
    have : ((QuotientGroup.mk g₂ * (QuotientGroup.mk g₁)⁻¹)⁻¹ *
          (QuotientGroup.mk g : PSL(2, ℤ)))⁻¹ * QuotientGroup.mk g₁ =
        (QuotientGroup.mk g : PSL(2, ℤ))⁻¹ * QuotientGroup.mk g₂ := by group
    rw [this]; exact hq_eq_g₂

open CongruenceSubgroup Classical in
/-- **Phase M (b) — uniform fiber cardinality of `slToPslQuot_Gamma_p_α`.**

Computed at the identity coset.  By
`slToPslQuot_Gamma_p_α_fiber_card_uniform`, every fiber has this cardinality. -/
noncomputable def slToPslQuot_fiberCard_Gamma_p_α (α : GL (Fin 2) ℚ) : ℕ :=
  haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
  (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
    slToPslQuot_Gamma_p_α (N := N) α q =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α))).card

theorem slToPslQuot_fiberCard_Gamma_p_α_eq (α : GL (Fin 2) ℚ)
    (q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :
    haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
      slToPslQuot_Gamma_p_α (N := N) α q = q')).card =
    slToPslQuot_fiberCard_Gamma_p_α (N := N) α := by
  rw [slToPslQuot_fiberCard_Gamma_p_α]
  exact slToPslQuot_Gamma_p_α_fiber_card_uniform (N := N) α q' _

open CongruenceSubgroup UpperHalfPlane MeasureTheory in
/-- **Phase M (b) — fiber-invariance of the SL-tile integral at H = Γ_p(α).** -/
theorem setIntegral_SL_tile_eq_PSL_tile_Gamma_p_α (α : GL (Fin 2) ℚ)
    (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp =
      ∫ τ in ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ))⁻¹ •
        (fdo : Set ℍ), h τ ∂μ_hyp := by
  have h_quot_eq :
      (QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) =
      QuotientGroup.mk ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ)) := by
    have h1 : slToPslQuot_Gamma_p_α (N := N) α q =
        QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) := by
      conv_lhs => rw [← q.out_eq]
      rfl
    exact h1.symm.trans (slToPslQuot_Gamma_p_α (N := N) α q).out_eq.symm
  rw [QuotientGroup.eq] at h_quot_eq
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := h_quot_eq
  have h_eq_PSL : ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ)) =
      QuotientGroup.mk q.out * QuotientGroup.mk γ := by
    have h_mul : (QuotientGroup.mk q.out : PSL(2, ℤ)) *
        ((QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ *
          (slToPslQuot_Gamma_p_α (N := N) α q).out) =
        (slToPslQuot_Gamma_p_α (N := N) α q).out := by group
    rw [← h_mul, ← hγ_eq]
    rfl
  rw [show ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ) =
      ((QuotientGroup.mk γ : PSL(2, ℤ))⁻¹ •
        ((QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))) by
      rw [h_eq_PSL, mul_inv_rev, mul_smul]]
  have h_psl_q : ((QuotientGroup.mk q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ) =
      (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ) := by
    rw [show ((QuotientGroup.mk q.out : PSL(2, ℤ)))⁻¹ =
          (QuotientGroup.mk q.out⁻¹ : PSL(2, ℤ)) from
        (QuotientGroup.mk_inv _ _).symm]
    rfl
  have h_psl_γ : ((QuotientGroup.mk γ : PSL(2, ℤ)))⁻¹ •
        ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) =
      (γ : SL(2, ℤ))⁻¹ • ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) := by
    rw [show ((QuotientGroup.mk γ : PSL(2, ℤ)))⁻¹ =
          (QuotientGroup.mk γ⁻¹ : PSL(2, ℤ)) from
        (QuotientGroup.mk_inv _ _).symm]
    rfl
  rw [h_psl_q, h_psl_γ]
  symm
  rw [show ((γ⁻¹ : SL(2, ℤ)) • ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) : Set ℍ) =
      (fun τ ↦ (γ⁻¹ : SL(2, ℤ)) • τ) '' ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) from rfl,
    (measurePreserving_smul (γ⁻¹ : SL(2, ℤ)) μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]
  congr 1; ext τ
  exact h_inv γ⁻¹ ((Gamma_p_α (N := N) α).inv_mem hγ_mem) τ

open CongruenceSubgroup UpperHalfPlane MeasureTheory Classical in
/-- **Phase M (b) — SL→PSL fiber-sum reindexing for Γ_p(α)-invariant integrands.**

Mirror of `sum_SL_tile_eq_fiberwise_PSL_tile` (`PeterssonLevelN.lean:1099`)
at the Γ_p(α) subgroup. -/
theorem sum_SL_tile_eq_fiberwise_PSL_tile_Gamma_p_α (α : GL (Fin 2) ℚ)
    (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
        ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp =
      ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
        (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
          slToPslQuot_Gamma_p_α (N := N) α q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  calc ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ))⁻¹ •
            (fdo : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_eq_PSL_tile_Gamma_p_α (N := N) α h h_inv q
    _ = ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
          ∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
            slToPslQuot_Gamma_p_α (N := N) α q = q'),
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        (Finset.sum_fiberwise' Finset.univ
          (slToPslQuot_Gamma_p_α (N := N) α)
          (fun q' ↦ ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp)).symm
    _ = ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
            slToPslQuot_Gamma_p_α (N := N) α q = q')).card •
              ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        exact Finset.sum_const _

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (b) — `fd` ↔ `fdo` SL-tile integral equality at H = Γ_p(α).** -/
theorem setIntegral_SL_tile_fd_eq_fdo_Gamma_p_α
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  rw [show ((q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ) : Set ℍ) =
        (fun τ ↦ (q.out : SL(2, ℤ))⁻¹ • τ) '' (fd : Set ℍ) from rfl,
    (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _),
    show ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ) : Set ℍ) =
        (fun τ ↦ (q.out : SL(2, ℤ))⁻¹ • τ) '' (fdo : Set ℍ) from rfl,
    (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _),
    setIntegral_fd_eq_fdo]

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (b) — pairwise AE-disjointness of canonical PSL coset tiles for Γ_p(α).**

Analog of `aedisjoint_PSL_coset_tiles` (`PeterssonLevelN.lean:549`) at
H = image_Gamma_p_α_PSL.  Uses `isFundamentalDomain_fdo_PSL.aedisjoint`
on the distinct PSL representatives `q.out`. -/
theorem aedisjoint_PSL_coset_tiles_Gamma_p_α (α : GL (Fin 2) ℚ) :
    Pairwise (fun q₁ q₂ : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α =>
      MeasureTheory.AEDisjoint μ_hyp
        ((q₁.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))
        ((q₂.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))) := by
  intro q₁ q₂ hne
  have h_inv_ne : (q₁.out : PSL(2, ℤ))⁻¹ ≠ (q₂.out : PSL(2, ℤ))⁻¹ := by
    intro hg
    apply hne
    have h_out : (q₁.out : PSL(2, ℤ)) = q₂.out := inv_injective hg
    rw [← q₁.out_eq, ← q₂.out_eq, h_out]
  exact isFundamentalDomain_fdo_PSL.aedisjoint h_inv_ne

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (b) — null-measurability of canonical PSL coset tiles for Γ_p(α).**

Analog of `nullMeasurableSet_PSL_coset_tile` (`PeterssonLevelN.lean:562`)
at H = image_Gamma_p_α_PSL. -/
theorem nullMeasurableSet_PSL_coset_tile_Gamma_p_α
    (α : GL (Fin 2) ℚ)
    (q : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :
    MeasureTheory.NullMeasurableSet
      ((q.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ)) μ_hyp :=
  isFundamentalDomain_fdo_PSL.nullMeasurableSet_smul _

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (b) — `Gamma_p_α_fundDomain_PSL_canonical` integral as PSL-tile sum.**

Mirror of `setIntegral_Gamma1_fundDomain_PSL_eq_sum` (`PeterssonLevelN.lean:575`)
at the canonical Γ_p(α) PSL fundamental domain. -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_sum
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_int : IntegrableOn h
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp) :
    ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp =
      ∑ q : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
        ∫ τ in ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  rw [Gamma_p_α_fundDomain_PSL_canonical,
    integral_iUnion_ae
      (nullMeasurableSet_PSL_coset_tile_Gamma_p_α (N := N) α)
      (aedisjoint_PSL_coset_tiles_Gamma_p_α (N := N) α) h_int,
    tsum_fintype]

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (b) — main bridge: SL outer-q sum ↔ scaled `Gamma_p_α_fundDomain_PSL_canonical`
integral.** -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_SL_outer_q_sum
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (h_int : IntegrableOn h
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
    (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
      ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp := by
  classical
  calc ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_fd_eq_fdo_Gamma_p_α (N := N) α h q
    _ = ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
            slToPslQuot_Gamma_p_α (N := N) α q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        sum_SL_tile_eq_fiberwise_PSL_tile_Gamma_p_α (N := N) α h h_inv
    _ = (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
          ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        congr 1
        convert slToPslQuot_fiberCard_Gamma_p_α_eq (N := N) α q' using 2
        congr
    _ = (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
          ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp := by
        rw [← setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_sum
          (N := N) α h h_int]

open CongruenceSubgroup Pointwise in
/-- **Phase M (c) — `(Γ_p(α)).map SL2Z_to_PSL2R = (image_Gamma_p_α_PSL α).map PSL2Z_to_PSL2R`.**

Mirror of `map_SL2Z_to_PSL2R_eq_imageGamma1_PSL_R` (`PeterssonLevelN.lean:795`)
at the Γ_p(α) subgroup.  Identifies the direct integer-to-PSL(2, ℝ) map of
Γ_p(α) with the two-step composition through `image_Gamma_p_α_PSL α`. -/
theorem map_SL2Z_to_PSL2R_eq_image_Gamma_p_α_PSL_R
    (α : GL (Fin 2) ℚ) :
    (Gamma_p_α (N := N) α).map SL2Z_to_PSL2R =
      (image_Gamma_p_α_PSL (N := N) α).map PSL2Z_to_PSL2R := by
  unfold image_Gamma_p_α_PSL
  rw [Subgroup.map_map]
  rfl

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase M (c) — canonical FD is also a FD for `(Γ_p(α)).map SL2Z_to_PSL2R`.** -/
theorem isFundamentalDomain_Gamma_p_α_PSL_canonical_at_PSL_R
    (α : GL (Fin 2) ℚ) :
    IsFundamentalDomain ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp := by
  rw [map_SL2Z_to_PSL2R_eq_image_Gamma_p_α_PSL_R]
  have h_base : IsFundamentalDomain (image_Gamma_p_α_PSL (N := N) α)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp :=
    isFundamentalDomain_Gamma_p_α_PSL_canonical (N := N) α
  have h_image_eq : (Equiv.refl ℍ) '' (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) =
      Gamma_p_α_fundDomain_PSL_canonical (N := N) α := by
    simp
  rw [← h_image_eq]
  refine h_base.image_of_equiv (Equiv.refl ℍ)
    (MeasureTheory.Measure.QuasiMeasurePreserving.id μ_hyp)
    ((Subgroup.equivMapOfInjective (image_Gamma_p_α_PSL (N := N) α)
      PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.symm) ?_
  intro g τ
  show (Equiv.refl ℍ) (((Subgroup.equivMapOfInjective
        (image_Gamma_p_α_PSL (N := N) α) PSL2Z_to_PSL2R
        PSL2Z_to_PSL2R_injective).toEquiv.symm g :
        image_Gamma_p_α_PSL (N := N) α) • τ) =
      ((g : (image_Gamma_p_α_PSL (N := N) α).map PSL2Z_to_PSL2R) :
        PSL(2, ℝ)) • (Equiv.refl ℍ) τ
  simp only [Equiv.refl_apply]
  set g' : image_Gamma_p_α_PSL (N := N) α :=
    (Subgroup.equivMapOfInjective (image_Gamma_p_α_PSL (N := N) α)
      PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.symm g with hg'_def
  have h_g_coe :
      ((g : (image_Gamma_p_α_PSL (N := N) α).map PSL2Z_to_PSL2R) : PSL(2, ℝ)) =
        PSL2Z_to_PSL2R (g' : PSL(2, ℤ)) := by
    have : ((Subgroup.equivMapOfInjective (image_Gamma_p_α_PSL (N := N) α)
        PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective) g' : PSL(2, ℝ)) =
        PSL2Z_to_PSL2R (g' : PSL(2, ℤ)) :=
      Subgroup.coe_equivMapOfInjective_apply _ _ _ _
    rw [← this]
    congr 1
    exact ((Subgroup.equivMapOfInjective (image_Gamma_p_α_PSL (N := N) α)
      PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.apply_symm_apply g).symm
  rw [h_g_coe, PSL2Z_to_PSL2R_smul_eq]
  rfl

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase M (c) — Phase H domain is also a FD for `(Γ_p(α)).map SL2Z_to_PSL2R`.** -/
theorem isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R
    (α : GL (Fin 2) ℚ) :
    IsFundamentalDomain ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)
      (Gamma_p_α_fundDomain_PSL (N := N) α) μ_hyp := by
  have h_subgroupOf := Gamma_p_α_PSL_R_FD_finite_index_decomp_auto (N := N) α
  have h_le : ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) ≤
              ((Gamma1 N).map SL2Z_to_PSL2R) :=
    Subgroup.map_mono (Gamma_p_α_le_Gamma1 α)
  have h_image := h_subgroupOf.image_of_equiv (Equiv.refl ℍ)
    (MeasureTheory.Measure.QuasiMeasurePreserving.id _)
    ((Subgroup.subgroupOfEquivOfLe h_le).symm.toEquiv)
    (fun _ _ ↦ rfl)
  simp only [Equiv.coe_refl, Set.image_id] at h_image
  exact h_image

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase M (c) — `Γ_p(α)`-invariance lifts to `(Γ_p(α)).map SL2Z_to_PSL2R`-invariance.** -/
theorem inv_under_Gamma_p_α_PSL_R_of_inv_under_Gamma_p_α
    (α : GL (Fin 2) ℚ) {h : ℍ → ℂ}
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (g : ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)) (τ : ℍ) :
    h (g • τ) = h τ := by
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := g.property
  have h_smul : (g : PSL(2, ℝ)) • τ = γ • τ := by
    rw [← hγ_eq, SL2Z_to_PSL2R_smul]
    rfl
  show h ((g : PSL(2, ℝ)) • τ) = h τ
  rw [h_smul]
  exact h_inv γ hγ_mem τ

open CongruenceSubgroup Pointwise in
/-- **Phase M (c) — countability of the PSL(2, ℝ)-side image of `Γ_p(α)`.** -/
instance Gamma_p_α_PSL_R_countable
    (α : GL (Fin 2) ℚ) :
    Countable ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) := by
  classical
  let F : Gamma_p_α (N := N) α →
      ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) :=
    fun γ ↦ ⟨SL2Z_to_PSL2R (γ : SL(2, ℤ)),
      ⟨(γ : SL(2, ℤ)), γ.property, rfl⟩⟩
  exact Function.Surjective.countable (f := F) (by
    intro g
    rcases g.property with ⟨γ, hγ, hγ_eq⟩
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact Subtype.ext hγ_eq)

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase M (c) — integral equality between Phase H FD and canonical FD for
`Γ_p(α)`-invariant integrands.** -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_eq_canonical
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ) :
    ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α, h τ ∂μ_hyp =
      ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp :=
  (isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R (N := N) α).setIntegral_eq
    (isFundamentalDomain_Gamma_p_α_PSL_canonical_at_PSL_R (N := N) α)
    (fun g τ ↦ inv_under_Gamma_p_α_PSL_R_of_inv_under_Gamma_p_α (N := N) α h_inv g τ)

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase M (c) — main transfer: Γ_p(α) outer-SL bridge for the Phase H FD.** -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (h_int : IntegrableOn h
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (ModularGroup.fd : Set ℍ), h τ ∂μ_hyp =
    (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
      ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α, h τ ∂μ_hyp := by
  rw [setIntegral_Gamma_p_α_fundDomain_PSL_eq_canonical (N := N) α h h_inv]
  exact setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_SL_outer_q_sum
    (N := N) α h h_inv h_int

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (d) — `Gamma_p_α_fundDomain_PSL_canonical α` has finite measure.** -/
theorem hyperbolicMeasure_Gamma_p_α_fundDomain_PSL_canonical_lt_top
    (α : GL (Fin 2) ℚ) :
    μ_hyp (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) < ⊤ := by
  rw [Gamma_p_α_fundDomain_PSL_canonical]
  refine lt_of_le_of_lt (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun q' _ ↦ ?_
  have hmeas : μ_hyp ((q'.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ)) =
      μ_hyp (fdo : Set ℍ) :=
    (isFundamentalDomain_fdo_PSL.smul _).measure_eq isFundamentalDomain_fdo_PSL
  rw [hmeas]
  exact lt_of_le_of_lt (measure_mono fdo_subset_fd) hyperbolicMeasure_fd_lt_top

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (d) — Petersson kernel integrable on canonical Γ_p(α) FD.** -/
theorem integrableOn_petersson_Gamma_p_α_fundDomain_PSL_canonical
    (α : GL (Fin 2) ℚ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IntegrableOn (fun τ ↦ petersson k ⇑f ⇑g τ)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f g
  exact IntegrableOn.of_bound
    (hyperbolicMeasure_Gamma_p_α_fundDomain_PSL_canonical_lt_top (N := N) α)
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous g)).aestronglyMeasurable.restrict)
    C (ae_of_all _ fun τ ↦ hC τ)

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (d) — α-uniform Petersson specialization of the Γ_p(α) outer-SL bridge.** -/
theorem peterssonInner_petersson_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum
    (α : GL (Fin 2) ℚ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (ModularGroup.fd : Set ℍ),
        petersson k ⇑f ⇑g τ ∂μ_hyp =
    (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
      ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α,
        petersson k ⇑f ⇑g τ ∂μ_hyp :=
  setIntegral_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum
    (N := N) α
    (petersson k ⇑f ⇑g)
    (fun γ hγ_mem τ ↦ petersson_Gamma1_invariant f g γ ((Gamma_p_α_le_Gamma1 α) hγ_mem) τ)
    (integrableOn_petersson_Gamma_p_α_fundDomain_PSL_canonical (N := N) α f g)

open CongruenceSubgroup in
/-- **Phase M (e) — natural quotient map `SL ⧸ Γ_p(α) → SL ⧸ Γ₁(N)`.**

Sends each `Γ_p(α)`-coset `[g]` to its `Γ₁(N)`-coset `[g]`.  Well-defined by
the inclusion `Γ_p(α) ≤ Γ₁(N)` (`Gamma_p_α_le_Gamma1`). -/
noncomputable def slGamma_p_αToGamma1 (α : GL (Fin 2) ℚ) :
    SL(2, ℤ) ⧸ Gamma_p_α (N := N) α →
      SL(2, ℤ) ⧸ Gamma1 N :=
  Quotient.lift
    (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply (QuotientGroup.eq).mpr
      exact (Gamma_p_α_le_Gamma1 α) hab)

@[simp]
theorem slGamma_p_αToGamma1_mk (α : GL (Fin 2) ℚ) (g : SL(2, ℤ)) :
    slGamma_p_αToGamma1 (N := N) α
        (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
      QuotientGroup.mk g := rfl

theorem slGamma_p_αToGamma1_surjective (α : GL (Fin 2) ℚ) :
    Function.Surjective (slGamma_p_αToGamma1 (N := N) α) := by
  intro q'
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q'
  refine ⟨QuotientGroup.mk g, ?_⟩
  rw [slGamma_p_αToGamma1_mk, hg]

open CongruenceSubgroup Classical in
/-- **Phase M (e) — uniform fiber cardinality** of `slGamma_p_αToGamma1`.

Mirror of `slToPslQuot_Gamma_p_α_fiber_card_uniform` (Phase M(b)) at the
SL/Γ₁(N) target.  The proof uses the same left-multiplication bijection
between fibers, exploiting the SL-equivariance of the quotient map. -/
theorem slGamma_p_αToGamma1_fiber_card_uniform (α : GL (Fin 2) ℚ)
    (q₁' q₂' : SL(2, ℤ) ⧸ Gamma1 N) :
    haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
        slGamma_p_αToGamma1 (N := N) α q = q₁')).card =
      (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
        slGamma_p_αToGamma1 (N := N) α q = q₂')).card := by
  haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
  obtain ⟨q₁, hq₁⟩ := slGamma_p_αToGamma1_surjective (N := N) α q₁'
  obtain ⟨q₂, hq₂⟩ := slGamma_p_αToGamma1_surjective (N := N) α q₂'
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  set h := g₂ * g₁⁻¹ with hh_def
  refine Finset.card_bij'
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h q)
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h⁻¹ q)
    (fun q hq ↦ ?_) (fun q hq ↦ ?_)
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h⁻¹
        (slLeftMul_Gamma_p_α (N := N) α h q) = q
      rw [slLeftMul_Gamma_p_α_comp, inv_mul_cancel, slLeftMul_Gamma_p_α_one])
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h
        (slLeftMul_Gamma_p_α (N := N) α h⁻¹ q) = q
      rw [slLeftMul_Gamma_p_α_comp, mul_inv_cancel, slLeftMul_Gamma_p_α_one])
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slGamma_p_αToGamma1 (N := N) α (QuotientGroup.mk (h * g)) = q₂'
    rw [slGamma_p_αToGamma1_mk]
    have h_g₂ : (QuotientGroup.mk g₂ : SL(2, ℤ) ⧸ Gamma1 N) = q₂' := hq₂
    have h_g : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = q₁' := hq
    have h_g₁ : (QuotientGroup.mk g₁ : SL(2, ℤ) ⧸ Gamma1 N) = q₁' := hq₁
    rw [← h_g₂, hh_def, QuotientGroup.eq]
    have hq_eq : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = QuotientGroup.mk g₁ :=
      h_g.trans h_g₁.symm
    rw [QuotientGroup.eq] at hq_eq
    have : (g₂ * g₁⁻¹ * g)⁻¹ * g₂ = g⁻¹ * g₁ := by group
    rw [this]; exact hq_eq
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slGamma_p_αToGamma1 (N := N) α (QuotientGroup.mk (h⁻¹ * g)) = q₁'
    rw [slGamma_p_αToGamma1_mk]
    have h_g₁ : (QuotientGroup.mk g₁ : SL(2, ℤ) ⧸ Gamma1 N) = q₁' := hq₁
    have h_g : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = q₂' := hq
    have h_g₂ : (QuotientGroup.mk g₂ : SL(2, ℤ) ⧸ Gamma1 N) = q₂' := hq₂
    rw [← h_g₁, hh_def, QuotientGroup.eq]
    have hq_eq : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = QuotientGroup.mk g₂ :=
      h_g.trans h_g₂.symm
    rw [QuotientGroup.eq] at hq_eq
    have : ((g₂ * g₁⁻¹)⁻¹ * g)⁻¹ * g₁ = g⁻¹ * g₂ := by group
    rw [this]; exact hq_eq

open CongruenceSubgroup Classical in
/-- **Phase M (e) — uniform fiber cardinality** of `slGamma_p_αToGamma1` at identity. -/
noncomputable def slGamma_p_αToGamma1_fiberCard (α : GL (Fin 2) ℚ) : ℕ :=
  haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
  (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
    slGamma_p_αToGamma1 (N := N) α q =
      (QuotientGroup.mk (1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 N))).card

theorem slGamma_p_αToGamma1_fiberCard_eq (α : GL (Fin 2) ℚ)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) :
    haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
      slGamma_p_αToGamma1 (N := N) α q = q')).card =
    slGamma_p_αToGamma1_fiberCard (N := N) α := by
  rw [slGamma_p_αToGamma1_fiberCard]
  exact slGamma_p_αToGamma1_fiber_card_uniform (N := N) α q' _

open CongruenceSubgroup UpperHalfPlane MeasureTheory in
/-- **Phase M (e) — fiber-invariance of the SL-tile integral at H = Γ₁(N), Γ_p(α)-quotient.** -/
theorem setIntegral_SL_tile_Gamma_p_α_eq_SL_tile_Gamma1
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
      ∫ τ in ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ))⁻¹ •
        (fd : Set ℍ), h τ ∂μ_hyp := by
  have h_quot_eq : (QuotientGroup.mk q.out : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ)) := by
    have h1 : slGamma_p_αToGamma1 (N := N) α q = QuotientGroup.mk q.out := by
      conv_lhs => rw [← q.out_eq]
      rfl
    exact h1.symm.trans (slGamma_p_αToGamma1 (N := N) α q).out_eq.symm
  rw [QuotientGroup.eq] at h_quot_eq
  set γ := (q.out : SL(2, ℤ))⁻¹ * (slGamma_p_αToGamma1 (N := N) α q).out with hγ_def
  have hγ_mem : γ ∈ Gamma1 N := h_quot_eq
  have h_eq : ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ)) = q.out * γ := by
    rw [hγ_def]; group
  rw [show ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ))⁻¹ • (fd : Set ℍ) =
      ((q.out : SL(2, ℤ)) * γ)⁻¹ • (fd : Set ℍ) by rw [h_eq]]
  rw [show (((q.out : SL(2, ℤ)) * γ)⁻¹ • (fd : Set ℍ) : Set ℍ) =
      ((γ : SL(2, ℤ))⁻¹ • ((q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ))) by
    rw [mul_inv_rev, mul_smul]]
  symm
  rw [show ((γ⁻¹ : SL(2, ℤ)) • ((q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ)) : Set ℍ) =
      (fun τ ↦ (γ⁻¹ : SL(2, ℤ)) • τ) '' ((q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ)) from rfl,
    (measurePreserving_smul (γ⁻¹ : SL(2, ℤ)) μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]
  congr 1; ext τ
  exact h_inv γ⁻¹ ((Gamma1 N).inv_mem hγ_mem) τ

open CongruenceSubgroup UpperHalfPlane MeasureTheory Classical in
/-- **Phase M (e) — SL/Γ_p(α) → SL/Γ₁(N) fiber-sum reindex.** -/
theorem sum_SL_tile_Gamma_p_α_eq_fiberCard_mul_SL_tile_Gamma1
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
    (slGamma_p_αToGamma1_fiberCard (N := N) α) •
      ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
        ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp := by
  calc ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ))⁻¹ •
            (fd : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_Gamma_p_α_eq_SL_tile_Gamma1 (N := N) α h h_inv q
    _ = ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
          ∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
            slGamma_p_αToGamma1 (N := N) α q = q'),
            ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp :=
        (Finset.sum_fiberwise' Finset.univ
          (slGamma_p_αToGamma1 (N := N) α)
          (fun q' ↦ ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp)).symm
    _ = (slGamma_p_αToGamma1_fiberCard (N := N) α) •
          ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
            ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        rw [Finset.sum_const]
        congr 1
        convert slGamma_p_αToGamma1_fiberCard_eq (N := N) α q' using 2
        congr

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (f) — Petersson kernel: `Γ_p(α)` outer-SL sum equals `relIndex • petN`.** -/
theorem sum_SL_Gamma_p_α_setIntegral_fd_petersson_eq_relIndex_mul_petN
    (α : GL (Fin 2) ℚ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
        petersson k ⇑f ⇑g τ ∂μ_hyp =
    (slGamma_p_αToGamma1_fiberCard (N := N) α) • petN f g := by
  rw [sum_SL_tile_Gamma_p_α_eq_fiberCard_mul_SL_tile_Gamma1 (N := N) α
      (petersson k ⇑f ⇑g)
      (fun γ hγ τ ↦ petersson_Gamma1_invariant f g γ hγ τ)]
  congr 1
  show ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
        petersson k ⇑f ⇑g τ ∂μ_hyp = petN f g
  unfold petN
  refine Finset.sum_congr rfl fun q' _ ↦ ?_
  exact (petN_summand_eq_setIntegral f g q').symm

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (g) prelude — generic SL-element petersson-fd-slash setIntegral identity.** -/
theorem peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd
    (F G : ℍ → ℂ) (s : SL(2, ℤ)) :
    peterssonInner k fd (F ∣[k] (s : SL(2, ℤ))⁻¹) (G ∣[k] (s : SL(2, ℤ))⁻¹) =
    ∫ τ in (s : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
      petersson k F G τ ∂μ_hyp := by
  simp only [peterssonInner]
  simp_rw [petersson_slash_SL]
  rw [← Set.image_smul,
    ← (measurePreserving_smul (s : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase M (g) — Petersson kernel: `Γ_p(α)` outer-SL `petN`-summand sum equals `relIndex • petN`.** -/
theorem sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN
    (α : GL (Fin 2) ℚ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      peterssonInner k (ModularGroup.fd : Set ℍ)
        (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) =
    (slGamma_p_αToGamma1_fiberCard (N := N) α) • petN f g := by
  rw [show (∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
        peterssonInner k (ModularGroup.fd : Set ℍ)
          (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹)
          (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹)) =
      ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
        ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
          petersson k ⇑f ⇑g τ ∂μ_hyp from
    Finset.sum_congr rfl fun q _ ↦ peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd ⇑f ⇑g q.out]
  exact sum_SL_Gamma_p_α_setIntegral_fd_petersson_eq_relIndex_mul_petN α f g

/-! ### SL₂(ℤ) continuity instance -/

private instance : ContinuousConstSMul SL(2, ℤ) UpperHalfPlane where
  continuous_const_smul c := by
    show Continuous fun τ ↦ (map (Int.castRingHom ℝ) c) • τ
    exact continuous_const_smul _

/-- Diamond operators are unitary for the **level-N Petersson inner product** `petN`:
`⟨⟨d⟩f, ⟨d⟩g⟩_N = ⟨f, g⟩_N`. -/
theorem diamondOp_petersson_unitary
    (d : (ZMod N)ˣ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k d f) (diamondOp_cusp k d g) = petN f g := by
  set γ_sub := (Gamma0MapUnits_surjective d).choose
  exact petN_slash_invariant f g (γ_sub : SL(2, ℤ)) γ_sub.property
    (fun η hη ↦ slash_Gamma1_eq f η hη) (fun η hη ↦ slash_Gamma1_eq g η hη)
    (diamondOp_cusp k d f) (diamondOp_cusp k d g) rfl rfl

/-! ### T_p adjoint via diamond unitarity

The symmetric Hecke adjoint `petN(T_p f, g) = petN(⟨p⟩f, T_p g)` is the hard
analytic/combinatorial core of DS Theorem 5.5.3. It requires:
- Stage A: Decomposing `petN(T_p f, g)` via linearity of `peterssonInner`
- Stage B: Applying `peterssonInner_slash_adjoint` + coset reindexing
- Stage C: Identifying adjugate reps with T_p reps via `adjointGamma0Rep`

The main theorem `heckeT_p_adjoint` reduces to this via `diamondOp_petersson_unitary`:
  `petN(T_p f, g) = petN(⟨p⟩f, T_p g) = petN(f, ⟨p⟩⁻¹ T_p g)`. -/

/-! ### GL₂⁺ coset adjoint lifted to petN

The symmetric Hecke adjoint (DS Theorem 5.5.3 core):
`petN(T_p f, g) = petN(⟨p⟩f, T_p g)`.

This is the symmetric form of the adjoint identity, equivalent to
`petN_heckeT_p_adjoint_unsymm` via `diamondOp_petersson_unitary`.

Proof sketch (DS §5.5): for each T_p coset representative `α_b ∈ GL₂⁺(ℚ)` and each
`Γ₁(N)`-coset `[q]`, apply `peterssonInner_slash_adjoint` to get:
```
  ∫_fd petersson k ((f∣α_b)∣q⁻¹) (g∣q⁻¹) dμ
    = ∫_{α_b•fd} petersson k (f∣q⁻¹) ((g∣q⁻¹)∣adj(α_b)) dμ
```
Then factor `adj(α_b) = γ₁ · α_{σ(b)} · γ₀` where `γ₁ ∈ Γ₁(N)`,
`σ` permutes the indices, and `γ₀ = adjointGamma0Rep` represents `⟨p⟩⁻¹`.
After `Γ₁(N)`-tile reindexing and the permutation `σ`, the sum reconstructs
as `petN(⟨p⟩f, T_p g)`.

GL₂⁺ coset adjoint lifted to petN (DS Proposition 5.5.2b):
for `α ∈ GL₂⁺(ℝ)` whose slash preserves `Γ₁(N)`-cuspidality,
`petN(f_α, g) = petN(f, g_{adj(α)})` where `f_α` has function `⇑f ∣[k] α`.

This lifts `peterssonInner_slash_adjoint` (the single-domain identity) to the
full `petN` coset sum. The proof requires showing that the shifted domains
`{α • (q.out⁻¹ • fd)}_{q}` tile a `Γ₁(N)`-fundamental domain, which follows
from `Gamma0_normalizes_Gamma1` and `measurePreserving_smul` but requires
`IsFundamentalDomain` infrastructure for the quotient `Γ₁(N) \ ℍ`. -/

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Fundamental domain tiling identity** for `GL₂⁺(ℝ)` shifts. -/
theorem sum_setIntegral_GL2_shift
    (α : GL(2, ℝ)⁺) (h : UpperHalfPlane → ℂ)
    (h_inv : ∀ (γ : SL(2, ℤ)), γ ∈ Gamma1 N →
      ∀ τ : UpperHalfPlane, h (γ • τ) = h τ)
    (hα_h_inv : ∀ (γ : SL(2, ℤ)), γ ∈ Gamma1 N →
      ∀ τ : UpperHalfPlane,
        h ((α : GL (Fin 2) ℝ) • ((γ : SL(2, ℤ)) • τ)) =
        h ((α : GL (Fin 2) ℝ) • τ))
    (hα_fd : IsFundamentalDomain (imageGamma1_PSL N)
      ((α : GL (Fin 2) ℝ) • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (h_int : IntegrableOn h (Gamma1_fundDomain_PSL N) μ_hyp)
    (h_α_int : IntegrableOn (fun τ ↦ h ((α : GL (Fin 2) ℝ) • τ))
      (Gamma1_fundDomain_PSL N) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (↑α : GL (Fin 2) ℝ) •
          ((q.out : SL(2, ℤ))⁻¹ • (ModularGroup.fd : Set UpperHalfPlane)),
        h τ ∂hyperbolicMeasure =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (ModularGroup.fd : Set UpperHalfPlane),
        h τ ∂hyperbolicMeasure := by
  set h_α : ℍ → ℂ := fun τ ↦ h ((α : GL (Fin 2) ℝ) • τ) with h_α_def
  have h_α_inv : ∀ (γ : SL(2, ℤ)), γ ∈ Gamma1 N →
      ∀ τ : UpperHalfPlane, h_α (γ • τ) = h_α τ := hα_h_inv
  have h_LHS_cov : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (↑α : GL (Fin 2) ℝ) •
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)),
        h τ ∂μ_hyp =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane), h_α τ ∂μ_hyp := by
    intro q
    rw [show ((↑α : GL (Fin 2) ℝ) • ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)) :
          Set UpperHalfPlane) =
        (fun τ ↦ (α : GL(2, ℝ)⁺) • τ) ''
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)) by
        rw [Set.image_smul]; rfl]
    exact (measurePreserving_smul α μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul α) _ _
  simp_rw [h_LHS_cov]
  classical
  have gen_SL_fd_sum_eq : ∀ (φ : ℍ → ℂ)
      (_ : ∀ (γ : SL(2, ℤ)), γ ∈ Gamma1 N → ∀ τ : UpperHalfPlane, φ (γ • τ) = φ τ)
      (_ : IntegrableOn φ (Gamma1_fundDomain_PSL N) μ_hyp),
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane), φ τ ∂μ_hyp =
      (slToPslQuot_fiberCard N) • ∫ τ in Gamma1_fundDomain_PSL N, φ τ ∂μ_hyp := by
    intro φ φ_inv φ_int
    calc ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
            ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane), φ τ ∂μ_hyp
        = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
            ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set UpperHalfPlane), φ τ ∂μ_hyp :=
          Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_fd_eq_fdo φ q
      _ = ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
            (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q')).card •
              ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set UpperHalfPlane), φ τ ∂μ_hyp :=
          sum_SL_tile_eq_fiberwise_PSL_tile φ φ_inv
      _ = (slToPslQuot_fiberCard N) • ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set UpperHalfPlane), φ τ ∂μ_hyp := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun q' _ ↦ ?_
          congr 1
          convert slToPslQuot_fiberCard_eq q' using 2
          congr
      _ = (slToPslQuot_fiberCard N) • ∫ τ in Gamma1_fundDomain_PSL N, φ τ ∂μ_hyp := by
          rw [← setIntegral_Gamma1_fundDomain_PSL_eq_sum φ φ_int]
  rw [gen_SL_fd_sum_eq h_α h_α_inv h_α_int,
      gen_SL_fd_sum_eq h h_inv h_int]
  congr 1
  rw [show ∫ τ in Gamma1_fundDomain_PSL N, h_α τ ∂μ_hyp =
        ∫ τ in ((↑α : GL (Fin 2) ℝ) • (Gamma1_fundDomain_PSL N : Set ℍ) : Set ℍ),
          h τ ∂μ_hyp by
    rw [show ((↑α : GL (Fin 2) ℝ) • (Gamma1_fundDomain_PSL N : Set ℍ) : Set ℍ) =
        (fun τ ↦ (α : GL(2, ℝ)⁺) • τ) '' (Gamma1_fundDomain_PSL N : Set ℍ) by
        rw [Set.image_smul]; rfl]
    exact ((measurePreserving_smul α μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul α) _ _).symm]
  refine hα_fd.setIntegral_eq isFundamentalDomain_Gamma1_PSL ?_
  intro g τ
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := Subgroup.mem_map.mp g.property
  have h_act_eq : ((g : imageGamma1_PSL N) : PSL(2, ℤ)) • τ = γ • τ := by
    rw [← hγ_eq]; exact PSL_smul_coe γ τ
  show h (((g : imageGamma1_PSL N) : PSL(2, ℤ)) • τ) = h τ
  rw [h_act_eq]
  exact h_inv γ hγ_mem τ

open UpperHalfPlane ModularGroup MeasureTheory in
theorem petN_slash_adjoint_GL2
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (f_α : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_α : ⇑f_α = ⇑f ∣[k] α)
    (g_adj : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_adj : ⇑g_adj = ⇑g ∣[k] peterssonAdj α)
    (hα_norm : ∀ (γ : SL(2, ℤ)), γ ∈ Gamma1 N →
      ∀ τ : ℍ, petersson k ⇑f ⇑g_adj (α • ((γ : SL(2, ℤ)) • τ)) =
        petersson k ⇑f ⇑g_adj (α • τ))
    (hα_fd : IsFundamentalDomain (imageGamma1_PSL N)
      (α • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (h_int : IntegrableOn (petersson k ⇑f ⇑g_adj) (Gamma1_fundDomain_PSL N) μ_hyp)
    (h_α_int : IntegrableOn (fun τ ↦ petersson k ⇑f ⇑g_adj (α • τ))
      (Gamma1_fundDomain_PSL N) μ_hyp) :
    petN f_α g = petN f g_adj := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k fd (⇑f_α ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g_adj ∣[k] (q.out)⁻¹)
  have h_lhs : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k fd (⇑f_α ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹) =
      ∫ τ in α • ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)),
        petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ ∂μ_hyp := fun q ↦ by
    calc peterssonInner k fd (⇑f_α ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹)
        = ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
            petersson k ⇑f_α ⇑g τ ∂μ_hyp := petN_summand_eq_setIntegral f_α g q
      _ = ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
            petersson k (⇑f ∣[k] α) ⇑g τ ∂μ_hyp := by rw [hf_α]
      _ = peterssonInner k ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))
            (⇑f ∣[k] α) ⇑g := rfl
      _ = peterssonInner k (α • ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
            ⇑f (⇑g ∣[k] peterssonAdj α) :=
          peterssonInner_slash_adjoint _ α hα ⇑f ⇑g
      _ = ∫ τ in α • ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)),
            petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ ∂μ_hyp := rfl
  have h_rhs : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g_adj ∣[k] (q.out)⁻¹) =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
        petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ ∂μ_hyp := fun q ↦ by
    calc peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g_adj ∣[k] (q.out)⁻¹)
        = ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
            petersson k ⇑f ⇑g_adj τ ∂μ_hyp := petN_summand_eq_setIntegral f g_adj q
      _ = ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
            petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ ∂μ_hyp := by rw [hg_adj]
  simp_rw [h_lhs, h_rhs]
  refine sum_setIntegral_GL2_shift ⟨α, hα⟩
    (fun τ ↦ petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ)
    (fun γ hγ τ ↦ by
      show petersson k ⇑f (⇑g ∣[k] peterssonAdj α) (γ • τ) =
        petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ
      rw [← hg_adj]; exact petersson_Gamma1_invariant f g_adj γ hγ τ)
    (fun γ hγ τ ↦ by rw [← hg_adj]; exact hα_norm γ hγ τ) hα_fd ?_ ?_
  ·
    simpa [hg_adj] using h_int
  ·
    simpa [hg_adj] using h_α_int

/-! ### Summand-level adjoint identity

The proof of `petN(T_p f, g) = petN(⟨p⟩f, T_p g)` works at the `peterssonInner` summand
level. For each coset `[q]` in `SL₂(ℤ)/Γ₁(N)`, the `petN` summand decomposes:

```
peterssonInner k fd ((T_p f)∣q⁻¹) (g∣q⁻¹)
= Σ_b peterssonInner k fd (f∣α_b∣q⁻¹) (g∣q⁻¹) + peterssonInner k fd ((⟨p⟩f)∣α_∞∣q⁻¹) (g∣q⁻¹)
```

by linearity of `peterssonInner` in the first argument. Then `peterssonInner_slash_adjoint`
(fully proved, no sorry) gives for each term:

```
peterssonInner k fd (f∣(α_b * q⁻¹)) (g∣q⁻¹)
= peterssonInner k ((α_b * q⁻¹) • fd) f ((g∣q⁻¹)∣adj(α_b * q⁻¹))
```

The key algebraic identities:
* `adj(T_p_upper(b)) = [[p,-b],[0,1]] = [[1,-b],[0,1]] · [[p,0],[0,1]]`
  where `[[1,-b],[0,1]] ∈ Γ₁(N)`, so for `g ∈ S_k(Γ₁(N))`:
  `g∣adj(T_p_upper(b)) = g∣T_p_lower` (b-independent).
* `adj(T_p_lower) = [[1,0],[0,p]] = T_p_upper(0)`.
* From `adjointGamma0Rep`: `T_p_lower = γ₁⁻¹ · T_p_upper(0) · γ₀`
  where `γ₁ ∈ Γ₁(N)` and `Gamma0MapUnits(γ₀) = ⟨p⟩⁻¹`.

The domain tiling after change of variables reassembles the integrals into `petN` for
the RHS. This tiling step requires `Γ₁(N)` fundamental domain infrastructure. -/

private lemma peterssonAdj_glMap_T_p_upper (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (peterssonAdj (glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), -(b : ℝ); 0, 1] := by
  rw [peterssonAdj_coe]
  have hcoe : (glMap (T_p_upper p hp b) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [glMap, T_p_upper]
  rw [hcoe, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply]

private lemma peterssonAdj_glMap_T_p_lower (p : ℕ) (hp : 0 < p) :
    (peterssonAdj (glMap (T_p_lower p hp)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), 0; 0, (p : ℝ)] := by
  rw [peterssonAdj_coe]
  have hcoe : (glMap (T_p_lower p hp) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), 0; 0, (1 : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [glMap, T_p_lower]
  rw [hcoe, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply]

/-- **T106 helper (GL₂(ℝ)-level)**: `peterssonAdj (glMap T_p_lower) = glMap T_p_upper(0)`.

Both are `GL (Fin 2) ℝ` elements with matrix `[[1, 0], [0, p]]`. Provides the
GL-level identity needed downstream when `adj(T_p_lower)` must be compared to
`T_p_upper(0)` as group elements (not just as matrices). -/
theorem peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero
    (p : ℕ) (hp : 0 < p) :
    peterssonAdj (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  have h_L := peterssonAdj_glMap_T_p_lower p hp
  have h_R : ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), 0; 0, (p : ℝ)] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.map, Matrix.of_apply]
  show (peterssonAdj (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix _ _ ℝ) i j =
    ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) : Matrix _ _ ℝ) i j
  rw [h_L, h_R]

/-- **T106 helper**: `glMap (mapGL ℚ γ) = mapGL ℝ γ` for `γ : SL(2, ℤ)`.

Composition of `SL(2, ℤ) → GL(2, ℚ) → GL(2, ℝ)` via `glMap ∘ mapGL ℚ` equals
the direct `SL(2, ℤ) → GL(2, ℝ)` map `mapGL ℝ`. Follows from Mathlib's
`map_mapGL` for `SpecialLinearGroup`. -/
theorem glMap_mapGL_Q_eq_mapGL_R (γ : SL(2, ℤ)) :
    (glMap ((mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ) γ) : GL (Fin 2) ℝ) =
      (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ := by
  apply Units.ext
  ext i j
  show ((glMap ((mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ) γ) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) i j =
    (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ) : Matrix (Fin 2) (Fin 2) ℝ) i j
  simp [glMap, Matrix.GeneralLinearGroup.map, mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map, algebraMap_int_eq, Matrix.map_apply]

private lemma glMap_M_infty_eq_mapGL_sigma_p_mul_glMap_T_p_lower
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ) *
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) := by
  rw [show (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap ((mapGL ℚ : SL(2, ℤ) →* _) (sigma_p_specific N p hp hpN)) *
        glMap (T_p_lower p hp) : GL (Fin 2) ℝ) by
    rw [← map_mul]; exact congr_arg _
      (M_infty_eq_sigma_mul_T_p_lower N p hp hpN)]
  rw [glMap_mapGL_Q_eq_mapGL_R]

/-- **T106 M_∞ adjoint helper**: `peterssonAdj (glMap M_∞) =
glMap T_p_upper(0) * mapGL ℝ σ_p⁻¹`. -/
theorem peterssonAdj_glMap_M_infty_eq
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    peterssonAdj (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _) (sigma_p_specific N p hp hpN)⁻¹) := by
  rw [show (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap ((mapGL ℚ : SL(2, ℤ) →* _) (sigma_p_specific N p hp hpN)) *
        glMap (T_p_lower p hp) : GL (Fin 2) ℝ) by
    rw [← map_mul]; exact congr_arg _
      (M_infty_eq_sigma_mul_T_p_lower N p hp hpN)]
  rw [peterssonAdj_mul]
  rw [peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero]
  rw [glMap_mapGL_Q_eq_mapGL_R]
  rw [peterssonAdj_mapGL_SL_eq_inv]
  rw [← map_inv]

private theorem peterssonAdj_glMap_M_infty_eq_via_gamma1
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    peterssonAdj (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _)
          ((gamma1_of_gamma0_sigma_p p N hp hpN : Gamma1 N) : SL(2, ℤ))⁻¹) *
        ((mapGL ℝ : SL(2, ℤ) →* _)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
  rw [peterssonAdj_glMap_M_infty_eq N p hp hpN,
    sigma_p_inv_eq_gamma1_inv_mul_gamma0 p N hp hpN, map_mul, ← mul_assoc]

private def shiftSL_loc (m : ℤ) : SL(2, ℤ) :=
  ⟨!![1, m; 0, 1], by simp [Matrix.det_fin_two]⟩

private lemma shiftSL_loc_mem_Gamma1 (m : ℤ) : shiftSL_loc m ∈ Gamma1 N := by
  rw [Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [shiftSL_loc]

private lemma peterssonAdj_T_p_upper_eq_shift_mul_lower
    (p : ℕ) (hp : 0 < p) (b : ℕ) :
    peterssonAdj (glMap (T_p_upper p hp b)) =
      (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) *
        glMap (T_p_lower p hp) := by
  apply Units.ext; ext i j
  have h_lhs : (peterssonAdj (glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), -(b : ℝ); 0, 1] := peterssonAdj_glMap_T_p_upper p hp b
  have h_rhs : ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) *
      glMap (T_p_lower p hp) : GL (Fin 2) ℝ).val =
      (!![(p : ℝ), -(b : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [shiftSL_loc, glMap, T_p_lower, mapGL, Matrix.SpecialLinearGroup.map,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Units.val_mul]
  show (peterssonAdj (glMap (T_p_upper p hp b)) : Matrix _ _ ℝ) i j =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) *
      glMap (T_p_lower p hp) : GL (Fin 2) ℝ).val i j
  rw [h_lhs, h_rhs]

private lemma slash_peterssonAdj_T_p_upper_eq_T_p_lower
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (T_p_upper p hp.pos b)) =
      ⇑g ∣[k] glMap (T_p_lower p hp.pos) := by
  rw [peterssonAdj_T_p_upper_eq_shift_mul_lower p hp.pos b,
      SlashAction.slash_mul]
  congr 1
  change ⇑g ∣[k] (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) = ⇑g
  have : (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) =
      (shiftSL_loc (-(b : ℤ)) : GL (Fin 2) ℝ) := rfl
  rw [this, ← ModularForm.SL_slash]
  exact slash_Gamma1_eq g _ (shiftSL_loc_mem_Gamma1 _)

private lemma slash_peterssonAdj_T_p_lower_eq_T_p_upper_0
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (T_p_lower p hp.pos)) =
      ⇑g ∣[k] glMap (T_p_upper p hp.pos 0) := by
  congr 1
  apply Units.ext; ext i j
  have h1 := peterssonAdj_glMap_T_p_lower p hp.pos
  have h2 : (glMap (T_p_upper p hp.pos 0) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), 0; 0, (p : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [glMap, T_p_upper]
  rw [show (peterssonAdj (glMap (T_p_lower p hp.pos)) : Matrix _ _ ℝ) i j =
      (!![(1 : ℝ), 0; 0, (p : ℝ)]) i j by rw [h1]]
  rw [show (glMap (T_p_upper p hp.pos 0) : Matrix _ _ ℝ) i j =
      (!![(1 : ℝ), 0; 0, (p : ℝ)]) i j by rw [h2]]

private lemma T_p_lower_triple_product_matrix (p N : ℕ) [NeZero N] (hp : 0 < p)
    (hpN : Nat.Coprime p N) :
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (adjointGamma1Rep p N hpN)) *
      (glMap (T_p_upper p hp 0)) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
  apply Units.ext; ext i j
  have h_lhs : (glMap (T_p_lower p hp) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), 0; 0, 1] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;> simp [glMap, T_p_lower]
  have hbez : (p : ℤ) * Int.gcdA p N + Int.gcdB p N * N = 1 := by
    have h := Int.gcd_eq_gcd_ab p N
    rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at h
    linarith
  have hbezℝ : (p : ℝ) * (Int.gcdA p N : ℝ) + (Int.gcdB p N : ℝ) * (N : ℝ) = 1 := by
    have := congr_arg (Int.cast : ℤ → ℝ) hbez
    push_cast at this; linarith
  have h_rhs : ((((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (adjointGamma1Rep p N hpN)) *
      (glMap (T_p_upper p hp 0))) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) :
      GL (Fin 2) ℝ).val =
      (!![(p : ℝ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i' j'
    fin_cases i' <;> fin_cases j' <;>
      simp [adjointGamma1Rep, adjointGamma0Rep, glMap, T_p_upper,
        mapGL, Matrix.SpecialLinearGroup.map,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Units.val_mul] <;>
      nlinarith [hbezℝ]
  show (glMap (T_p_lower p hp) : Matrix _ _ ℝ) i j =
    ((((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (adjointGamma1Rep p N hpN)) *
        (glMap (T_p_upper p hp 0))) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) : GL (Fin 2) ℝ).val i j
  rw [h_lhs, h_rhs]

private lemma slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0_ModularForm
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) =
      (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
  rw [show (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (adjointGamma1Rep p N hpN)) *
      (glMap (T_p_upper p hp.pos 0)) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) from
    T_p_lower_triple_product_matrix p N hp.pos hpN]
  rw [SlashAction.slash_mul, SlashAction.slash_mul]
  congr 2
  have hmem : (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (adjointGamma1Rep p N hpN) ∈
      (Gamma1 N).map (mapGL ℝ) :=
    ⟨adjointGamma1Rep p N hpN, adjointGamma1Rep_mem_Gamma1 p N hpN, rfl⟩
  exact SlashInvariantFormClass.slash_action_eq f _ hmem

private lemma slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) =
      (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) :=
  slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0_ModularForm p hp hpN f.toModularForm'

private lemma slash_peterssonAdj_T_p_upper_adjointGamma0Rep_inv_eq_T_p_upper_zero
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑f ∣[k] peterssonAdj (glMap (T_p_upper p hp.pos b))) ∣[k]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))⁻¹ :
          GL (Fin 2) ℝ) =
    ⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ) := by
  rw [peterssonAdj_T_p_upper_eq_shift_mul_lower p hp.pos b]
  rw [T_p_lower_triple_product_matrix p N hp.pos hpN]
  rw [SlashAction.slash_mul, SlashAction.slash_mul, SlashAction.slash_mul]
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  rw [show (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (shiftSL_loc (-(b : ℤ)))) : UpperHalfPlane → ℂ) = ⇑f from
      SlashInvariantFormClass.slash_action_eq f _
        (Subgroup.mem_map.mpr ⟨_, shiftSL_loc_mem_Gamma1 _, rfl⟩)]
  rw [show (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (adjointGamma1Rep p N hpN)) : UpperHalfPlane → ℂ) = ⇑f from
      SlashInvariantFormClass.slash_action_eq f _
        (Subgroup.mem_map.mpr
          ⟨_, adjointGamma1Rep_mem_Gamma1 p N hpN, rfl⟩)]

private lemma slash_peterssonAdj_T_p_upper_eq_slash_T_p_upper_zero_slash_gamma0
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (T_p_upper p hp.pos b)) =
    (⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
  rw [← slash_peterssonAdj_T_p_upper_adjointGamma0Rep_inv_eq_T_p_upper_zero
        p hp hpN b g,
      ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
private lemma slash_diamond_inv_M_infty_eq_slash_T_p_lower
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      ⇑f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
  set u := ZMod.unitOfCoprime p hpN
  rw [show ⇑(diamondOp k u⁻¹ f) ∣[k]
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      ⇑(diamondOp k u⁻¹ f) ∣[k]
        (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) from rfl]
  rw [slash_M_infty_eq_diamond_slash_T_p_lower k p hp.pos hpN
    (diamondOp k u⁻¹ f)]
  rw [show ⇑(diamondOp k u (diamondOp k u⁻¹ f)) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
      ⇑(diamondOp k u (diamondOp k u⁻¹ f)) ∣[k]
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) from rfl]
  have h_cancel : diamondOp k u (diamondOp k u⁻¹ f) = f := by
    show ((diamondOp k u).comp (diamondOp k u⁻¹)) f = f
    rw [← diamondOp_mul, mul_inv_cancel, diamondOp_one]; rfl
  rw [show ⇑(diamondOp k u (diamondOp k u⁻¹ f)) = ⇑f from
    congr_arg DFunLike.coe h_cancel]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_diamond_inv_M_infty_eq_T_p_lower
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (G : ℍ → ℂ) :
    peterssonInner k D
        (⇑(diamondOp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) G =
      peterssonInner k D
        (⇑f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) G := by
  rw [slash_diamond_inv_M_infty_eq_slash_T_p_lower p hp hpN f]

private lemma slash_diamond_inv_M_infty_eq_slash_T_p_lower_cusp
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      ⇑f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) :=
  slash_diamond_inv_M_infty_eq_slash_T_p_lower p hp hpN f.toModularForm'

private lemma slash_M_infty_eq_diamond_slash_T_p_lower_cusp_g
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
  rw [show ⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
        ⇑g ∣[k] (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) from rfl]
  exact slash_M_infty_eq_diamond_slash_T_p_lower k p hp.pos hpN g.toModularForm'

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_slash_M_infty_eq_diamond_T_p_lower_cusp_g
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F : ℍ → ℂ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k D F
        (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) =
      peterssonInner k D F
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  rw [slash_M_infty_eq_diamond_slash_T_p_lower_cusp_g p hp hpN g]

/-- **T127 residual M_∞-term reducing helper**: the T205 post-simp-chain
form `(⟨u⟩ f) ∣ T_p_upper(0) ∣ γ₀` equals the original `f ∣ M_∞` (reverse of
the two-step simp normalization used in T205). -/
theorem slash_diamond_T_p_upper_zero_slash_adjointGamma0Rep_eq_slash_M_infty
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) =
    ⇑f ∣[k] (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) := by
  rw [← slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0_ModularForm p hp hpN
    (diamondOp k (ZMod.unitOfCoprime p hpN) f)]
  rw [show ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) =
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) from rfl]
  rw [← slash_M_infty_eq_diamond_slash_T_p_lower k p hp.pos hpN f]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_slash_adjoint_coset
    (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val) (q : SL(2, ℤ)) (f g : ℍ → ℂ) :
    peterssonInner k fd
        (f ∣[k] (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)))
        (g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) =
      peterssonInner k
        (β • ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)))
        f
        (g ∣[k] peterssonAdj β) := by
  have hq_det_mat : ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    have hcast : ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix (q⁻¹).val) := by
      rw [mapGL_coe_matrix]; rfl
    rw [hcast, ← RingHom.map_det, (q⁻¹).property]; simp
  have hdet_pos : 0 < (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)).det.val := by
    show 0 < (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) : GL (Fin 2) ℝ).val.det
    rw [Units.val_mul, Matrix.det_mul, hq_det_mat, mul_one]
    exact hβ
  have h_main := peterssonInner_slash_adjoint (k := k)
      (D := fd) (α := β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) hdet_pos
      f (g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ))
  have h_adj_prod : peterssonAdj (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) =
      (mapGL ℝ q : GL (Fin 2) ℝ) * peterssonAdj β := by
    rw [peterssonAdj_mul, peterssonAdj_mapGL_SL_eq_inv]
    congr 1
    rw [← map_inv, inv_inv]
  have h_slash_simp : ((g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) ∣[k]
        peterssonAdj (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ))) =
      g ∣[k] peterssonAdj β := by
    rw [h_adj_prod, ← SlashAction.slash_mul, ← mul_assoc]
    rw [show (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ q : GL (Fin 2) ℝ) = 1 by
      rw [← map_mul, inv_mul_cancel, map_one], one_mul]
  have h_domain : ((β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ) : Set ℍ) =
      (β • ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) : Set ℍ) :=
    mul_smul _ _ _
  rw [← h_slash_simp, ← h_domain]
  exact h_main

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_slash_adjoint_right (D : Set ℍ) (α : GL (Fin 2) ℝ)
    (hα : 0 < α.det.val) (f g : ℍ → ℂ) :
    peterssonInner k D f (g ∣[k] α) =
      peterssonInner k (α • D) (f ∣[k] peterssonAdj α) g := by
  have h1 := peterssonInner_conj_symm k D f (g ∣[k] α)
  have h2 := peterssonInner_slash_adjoint (k := k) D α hα g f
  have h3 := peterssonInner_conj_symm k (α • D) (f ∣[k] peterssonAdj α) g
  rw [← h1, h2, h3]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_slash_adj_T_p_upper_q_summand_eq
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  have hdet_pos : 0 < (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ).det.val := by
    show 0 < ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp.pos
  rw [peterssonInner_slash_adjoint_coset (glMap (T_p_upper p hp.pos b))
        hdet_pos q ⇑f ⇑g]
  rw [slash_peterssonAdj_T_p_upper_eq_slash_T_p_upper_zero_slash_gamma0 p hp hpN b g]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma sum_peterssonInner_upper_family_per_b_rewrite
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ b ∈ Finset.range p,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) =
    ∑ b ∈ Finset.range p,
      peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set UpperHalfPlane)))
        ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) :=
  Finset.sum_congr rfl fun b _ ↦ peterssonInner_slash_adj_T_p_upper_q_summand_eq p hp hpN b q f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_add_left (D : Set ℍ) (f₁ f₂ g : ℍ → ℂ)
    (hf₁ : IntegrableOn (fun τ ↦ petersson k g f₁ τ) D μ_hyp)
    (hf₂ : IntegrableOn (fun τ ↦ petersson k g f₂ τ) D μ_hyp) :
    peterssonInner k D (f₁ + f₂) g =
      peterssonInner k D f₁ g + peterssonInner k D f₂ g := by
  have h1 := peterssonInner_conj_symm k D (f₁ + f₂) g
  have h2 := peterssonInner_add_right k D g f₁ f₂ hf₁ hf₂
  have h3a := peterssonInner_conj_symm k D f₁ g
  have h3b := peterssonInner_conj_symm k D f₂ g
  rw [← h1, h2, map_add, h3a, h3b]

open UpperHalfPlane ModularGroup MeasureTheory ConjAct Pointwise in
/-- **T205 integrability helper (mixed SL/GL slash bridge).**
For `Γ₁(N)` cusp forms `f, g`, a rational matrix `α : GL (Fin 2) ℚ`, and an
`SL(2, ℤ)` element `δ`, the petersson integrand
`petersson k (⇑f ∣[k] δ) ((⇑g ∣[k] α) ∣[k] δ)` is integrable on the
`SL(2, ℤ)`-fundamental domain `fd`. -/
theorem integrableOn_petersson_cuspform_mixed_slash_on_fd
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (α : GL (Fin 2) ℚ) (δ : SL(2, ℤ)) :
    IntegrableOn (fun τ ↦ UpperHalfPlane.petersson k (⇑f ∣[k] δ)
        ((⇑g ∣[k] ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ)) ∣[k] δ) τ)
      (ModularGroup.fd : Set UpperHalfPlane) μ_hyp := by
  rw [show (fun τ ↦ UpperHalfPlane.petersson k (⇑f ∣[k] δ)
        ((⇑g ∣[k] ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ)) ∣[k] δ) τ) =
      (fun τ ↦ UpperHalfPlane.petersson k ⇑f
        (⇑g ∣[k] ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ)) (δ • τ)) from
      funext fun τ ↦ petersson_slash_SL k _ _ δ τ]
  haveI hArith :
      ((toConjAct ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹) •
        ((Gamma1 N).map (mapGL ℝ))).IsArithmetic := by
    have h := Subgroup.IsArithmetic.conj ((Gamma1 N).map (mapGL ℝ)) α⁻¹
    have h_inv : ((α⁻¹ : GL (Fin 2) ℚ).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) =
        ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ := map_inv _ _
    rwa [h_inv] at h
  let g_tr : CuspForm
      ((toConjAct ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹) •
        ((Gamma1 N).map (mapGL ℝ))) k :=
    CuspForm.translate g ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ)
  have h_gtr_coe : (⇑g_tr : UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ) := rfl
  obtain ⟨C_f, hC_f⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f f
  obtain ⟨C_g, hC_g⟩ := CuspFormClass.petersson_bounded_left k _ g_tr g_tr
  have h_AM_GM : ∀ τ,
      ‖UpperHalfPlane.petersson k ⇑f
          (⇑g ∣[k] ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ)) τ‖ ≤
        (C_f + C_g) / 2 := by
    intro τ
    rw [← h_gtr_coe]
    have h_norm_ineq : ‖UpperHalfPlane.petersson k ⇑f ⇑g_tr τ‖ ≤
        (‖UpperHalfPlane.petersson k ⇑f ⇑f τ‖ +
         ‖UpperHalfPlane.petersson k ⇑g_tr ⇑g_tr τ‖) / 2 := by
      simp only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj]
      have h_im_nn : (0 : ℝ) ≤ ‖((τ.im : ℂ) ^ k)‖ := norm_nonneg _
      nlinarith [mul_nonneg (sq_nonneg (‖(⇑f) τ‖ - ‖(⇑g_tr) τ‖)) h_im_nn,
        sq_nonneg (‖(⇑f) τ‖ - ‖(⇑g_tr) τ‖), norm_nonneg (⇑f τ),
        norm_nonneg (⇑g_tr τ), h_im_nn]
    linarith [hC_f τ, hC_g τ]
  refine IntegrableOn.of_bound hyperbolicMeasure_fd_lt_top ?_ ((C_f + C_g) / 2) ?_
  ·
    refine ((petersson_continuous k (ModularFormClass.continuous f)
      ?_).comp (continuous_const_smul δ)).aestronglyMeasurable.restrict
    rw [← h_gtr_coe]
    exact ModularFormClass.continuous g_tr
  · exact ae_of_all _ fun τ ↦ h_AM_GM (δ • τ)

/-! ### T092 / T094: Finset-additivity, finite-union bridge, and T_p-specific
AE-disjointness (DS Theorem 5.5.2(b) / T205 instantiation) -/

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T092 helper: `petersson` is linear in its second argument over finite sums.** -/
theorem petersson_sum_right {ι : Type*} (s : Finset ι) (f : ℍ → ℂ)
    (g : ι → ℍ → ℂ) (τ : ℍ) :
    petersson k f (∑ i ∈ s, g i) τ = ∑ i ∈ s, petersson k f (g i) τ := by
  simp only [petersson, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T092 helper: Finset additivity of `peterssonInner` in the first arg.** -/
theorem peterssonInner_sum_left
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℍ → ℂ)
    (g : ℍ → ℂ) (D : Set ℍ)
    (h_int : ∀ i ∈ s, IntegrableOn (fun τ ↦ petersson k g (F i) τ) D μ_hyp) :
    peterssonInner k D (∑ i ∈ s, F i) g = ∑ i ∈ s, peterssonInner k D (F i) g := by
  induction s using Finset.induction_on with
  | empty => simp [peterssonInner_zero_left]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    have h_i := h_int i (Finset.mem_insert_self i t)
    have h_t := fun j hj ↦ h_int j (Finset.mem_insert_of_mem hj)
    have h_sum_int :
        IntegrableOn (fun τ ↦ petersson k g (∑ j ∈ t, F j) τ) D μ_hyp := by
      have h_eq :
          (fun τ ↦ petersson k g (∑ j ∈ t, F j) τ) =
            fun τ ↦ ∑ j ∈ t, petersson k g (F j) τ := by
        funext τ; exact petersson_sum_right t g F τ
      rw [h_eq]
      exact MeasureTheory.integrable_finset_sum _ h_t
    rw [peterssonInner_add_left D (F i) (∑ j ∈ t, F j) g h_i h_sum_int,
      ih h_t, Finset.sum_insert hi]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_add_finset_sum_left
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f0 : ℍ → ℂ) (F : ι → ℍ → ℂ) (g : ℍ → ℂ) (D : Set ℍ)
    (h0 : IntegrableOn (fun τ ↦ petersson k g f0 τ) D μ_hyp)
    (hF : ∀ i ∈ s, IntegrableOn (fun τ ↦ petersson k g (F i) τ) D μ_hyp) :
    peterssonInner k D (f0 + ∑ i ∈ s, F i) g =
      peterssonInner k D f0 g + ∑ i ∈ s, peterssonInner k D (F i) g := by
  have hsum : IntegrableOn (fun τ ↦ petersson k g (∑ i ∈ s, F i) τ) D μ_hyp := by
    rw [show (fun τ ↦ petersson k g (∑ i ∈ s, F i) τ) =
        (fun τ ↦ ∑ i ∈ s, petersson k g (F i) τ) by
      funext τ; exact petersson_sum_right s g F τ]
    exact MeasureTheory.integrable_finset_sum _ hF
  rw [peterssonInner_add_left D f0 (∑ i ∈ s, F i) g h0 hsum,
    peterssonInner_sum_left s F g D hF]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T128 helper**: Finset additivity of `peterssonInner` in the second argument
(slot-2 analog of `peterssonInner_sum_left`). -/
lemma peterssonInner_sum_right
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ℍ → ℂ) (G : ι → ℍ → ℂ) (D : Set ℍ)
    (h_int : ∀ i ∈ s, IntegrableOn (fun τ ↦ petersson k f (G i) τ) D μ_hyp) :
    peterssonInner k D f (∑ i ∈ s, G i) = ∑ i ∈ s, peterssonInner k D f (G i) := by
  induction s using Finset.induction_on with
  | empty => simp [peterssonInner_zero_right]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    have h_i := h_int i (Finset.mem_insert_self i t)
    have h_t := fun j hj ↦ h_int j (Finset.mem_insert_of_mem hj)
    have h_sum_int :
        IntegrableOn (fun τ ↦ petersson k f (∑ j ∈ t, G j) τ) D μ_hyp := by
      have h_eq :
          (fun τ ↦ petersson k f (∑ j ∈ t, G j) τ) =
            fun τ ↦ ∑ j ∈ t, petersson k f (G j) τ := by
        funext τ; exact petersson_sum_right t f G τ
      rw [h_eq]
      exact MeasureTheory.integrable_finset_sum _ h_t
    rw [peterssonInner_add_right k D f (G i) (∑ j ∈ t, G j) h_i h_sum_int,
      ih h_t, Finset.sum_insert hi]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_add_finset_sum_right
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ℍ → ℂ) (g0 : ℍ → ℂ) (G : ι → ℍ → ℂ) (D : Set ℍ)
    (h0 : IntegrableOn (fun τ ↦ petersson k f g0 τ) D μ_hyp)
    (hG : ∀ i ∈ s, IntegrableOn (fun τ ↦ petersson k f (G i) τ) D μ_hyp) :
    peterssonInner k D f (g0 + ∑ i ∈ s, G i) =
      peterssonInner k D f g0 + ∑ i ∈ s, peterssonInner k D f (G i) := by
  have hsum : IntegrableOn (fun τ ↦ petersson k f (∑ i ∈ s, G i) τ) D μ_hyp := by
    rw [show (fun τ ↦ petersson k f (∑ i ∈ s, G i) τ) =
        (fun τ ↦ ∑ i ∈ s, petersson k f (G i) τ) by
      funext τ; exact petersson_sum_right s f G τ]
    exact MeasureTheory.integrable_finset_sum _ hG
  rw [peterssonInner_add_right k D f g0 (∑ i ∈ s, G i) h0 hsum,
    peterssonInner_sum_right s f G D hG]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T092: sum-of-slashes adjoint (DS 5.5.2(b) slice).** -/
theorem peterssonInner_sum_slash_adjoint
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ) (hα : ∀ i ∈ s, 0 < (α i).det.val)
    (D : Set ℍ) (f g : ℍ → ℂ)
    (h_int : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k g (f ∣[k] α i) τ) D μ_hyp) :
    peterssonInner k D (∑ i ∈ s, f ∣[k] α i) g =
      ∑ i ∈ s, peterssonInner k ((α i) • D) f (g ∣[k] peterssonAdj (α i)) := by
  rw [peterssonInner_sum_left s (fun i ↦ f ∣[k] α i) g D h_int]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  exact peterssonInner_slash_adjoint D (α i) (hα i hi) f g

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T092 finite-union bridge (pure measure-theoretic form).** -/
theorem setIntegral_biUnion_finset_ae
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) {S : ι → Set X} {f : X → E}
    (hm : ∀ i ∈ s, NullMeasurableSet (S i) μ)
    (hd : (↑s : Set ι).Pairwise (fun i j ↦ AEDisjoint μ (S i) (S j)))
    (hfi : IntegrableOn f (⋃ i ∈ s, S i) μ) :
    ∫ x in ⋃ i ∈ s, S i, f x ∂μ = ∑ i ∈ s, ∫ x in S i, f x ∂μ := by
  classical
  have h_biU : (⋃ i ∈ s, S i) = ⋃ i : s, S i.val := by
    ext x; simp [Set.mem_iUnion]
  have hm' : ∀ i : s, NullMeasurableSet (S i.val) μ :=
    fun i ↦ hm i.val i.property
  have hd' : Pairwise (fun i j : s ↦ AEDisjoint μ (S i.val) (S j.val)) := by
    intro i j hij
    exact hd (Finset.mem_coe.mpr i.property) (Finset.mem_coe.mpr j.property)
      (fun h ↦ hij (Subtype.ext h))
  have hfi' : IntegrableOn f (⋃ i : s, S i.val) μ := by
    rw [← h_biU]; exact hfi
  rw [h_biU, integral_iUnion_ae hm' hd' hfi', tsum_fintype,
    Finset.sum_coe_sort s (fun i ↦ ∫ x in S i, f x ∂μ)]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T092 finite-union bridge (`peterssonInner` form).** -/
theorem peterssonInner_biUnion_finset_ae
    {ι : Type*} (s : Finset ι) {D : ι → Set ℍ}
    (hm : ∀ i ∈ s, NullMeasurableSet (D i) μ_hyp)
    (hd : (↑s : Set ι).Pairwise (fun i j ↦ AEDisjoint μ_hyp (D i) (D j)))
    (f g : ℍ → ℂ)
    (hfi : IntegrableOn (fun τ ↦ petersson k f g τ) (⋃ i ∈ s, D i) μ_hyp) :
    peterssonInner k (⋃ i ∈ s, D i) f g = ∑ i ∈ s, peterssonInner k (D i) f g :=
  setIntegral_biUnion_finset_ae s hm hd hfi

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T092: sum-of-slashes adjoint under constant-RHS hypothesis.** -/
theorem peterssonInner_sum_slash_adjoint_constantRHS
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ) (hα : ∀ i ∈ s, 0 < (α i).det.val)
    (D : Set ℍ) (f g g' : ℍ → ℂ)
    (hadj : ∀ i ∈ s, g ∣[k] peterssonAdj (α i) = g')
    (h_int : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k g (f ∣[k] α i) τ) D μ_hyp)
    (hm : ∀ i ∈ s, NullMeasurableSet ((α i) • D) μ_hyp)
    (hd : (↑s : Set ι).Pairwise
      (fun i j ↦ AEDisjoint μ_hyp ((α i) • D) ((α j) • D)))
    (hfi : IntegrableOn (fun τ ↦ petersson k f g' τ)
      (⋃ i ∈ s, (α i) • D) μ_hyp) :
    peterssonInner k D (∑ i ∈ s, f ∣[k] α i) g =
      peterssonInner k (⋃ i ∈ s, (α i) • D) f g' := by
  rw [peterssonInner_sum_slash_adjoint s α hα D f g h_int]
  rw [peterssonInner_biUnion_finset_ae s hm hd f g' hfi]
  exact Finset.sum_congr rfl fun i hi ↦ by rw [hadj i hi]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094 wrapper: AE-disjoint via PSL-coset `mul_inv_mem`.**  Direct
instantiation of `IsFundamentalDomain.aedisjoint_smul_of_mul_inv_mem` for
`Gamma1_fundDomain_PSL N`. -/
theorem aedisjoint_imageGamma1_PSL_smul_Gamma1_fundDomain
    {N : ℕ} [NeZero N] {q₁ q₂ : PSL(2, ℤ)}
    (h_mem : q₁⁻¹ * q₂ ∈ imageGamma1_PSL N) (h_ne : q₁⁻¹ * q₂ ≠ 1) :
    AEDisjoint μ_hyp (q₁ • (Gamma1_fundDomain_PSL N : Set ℍ))
      (q₂ • (Gamma1_fundDomain_PSL N : Set ℍ)) :=
  isFundamentalDomain_Gamma1_coset_tiling.aedisjoint_smul_of_mul_inv_mem
    h_mem h_ne

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094 helper: positive-det `GL (Fin 2) ℝ` elements are measure-preserving
on `ℍ` w.r.t. `μ_hyp`.** Lifts to `GL(2, ℝ)⁺` (positivity) and invokes
`measurePreserving_smul` with `instSMulInvMeasure_GLpos`. -/
theorem measurePreserving_glPos_smul (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val) :
    MeasurePreserving ((α • ·) : ℍ → ℍ) μ_hyp μ_hyp :=
  measurePreserving_smul (⟨α, hα⟩ : GL(2, ℝ)⁺) μ_hyp

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma integrableOn_petersson_slash_of_adj_image
    (D : Set ℍ) (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g g' : ℍ → ℂ)
    (hadj : g ∣[k] peterssonAdj α = g')
    (hfi : IntegrableOn (fun τ ↦ petersson k f g' τ) (α • D) μ_hyp) :
    IntegrableOn (fun τ ↦ petersson k g (f ∣[k] α) τ) D μ_hyp := by
  have hg_decomp : g = (g ∣[k] α⁻¹) ∣[k] α := by
    rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  set g_inv := g ∣[k] α⁻¹ with hg_inv_def
  have h_pointwise : ∀ τ, petersson k g (f ∣[k] α) τ =
      petersson k g' f (α • τ) := by
    intro τ
    rw [petersson_symm k (f ∣[k] α) g]
    conv_lhs => rw [show g = g_inv ∣[k] α from hg_decomp]
    rw [petersson_slash, show σ α = RingHom.id ℂ from if_pos hα, RingHom.id_apply]
    have h_scalar : (↑|α.det.val| ^ (k - 2) : ℂ) * petersson k f g_inv (α • τ) =
        petersson k f ((↑(|α.det.val| ^ (k - 2)) : ℂ) • g_inv) (α • τ) := by
      simp [petersson, Pi.smul_apply, smul_eq_mul]; ring
    rw [h_scalar]
    rw [show ((↑(|α.det.val| ^ (k - 2)) : ℂ) • g_inv) = g' by
      rw [← hadj, hg_inv_def, slash_peterssonAdj_eq α hα]]
    exact (petersson_symm k f g' (α • τ)).symm
  have h_fn_eq : (fun τ ↦ petersson k g (f ∣[k] α) τ) =
      fun τ ↦ petersson k g' f (α • τ) := funext h_pointwise
  rw [h_fn_eq]
  set α' : GL(2, ℝ)⁺ := ⟨α, hα⟩
  have h_α_eq : (α : GL (Fin 2) ℝ) • D = (fun τ ↦ α' • τ) '' D := by
    rw [Set.image_smul]; rfl
  rw [show (fun τ ↦ petersson k g' f (α • τ)) =
      petersson k g' f ∘ (fun τ ↦ α' • τ) from rfl]
  rw [← (measurePreserving_smul α' μ_hyp).integrableOn_image
      (measurableEmbedding_const_smul α')]
  rw [h_α_eq] at hfi
  have h_symm_fn : (petersson k g' f : ℍ → ℂ) =
      fun τ ↦ starRingEnd ℂ (petersson k f g' τ) :=
    funext fun τ ↦ petersson_symm k f g' τ
  rw [h_symm_fn]
  refine ⟨?_, ?_⟩
  ·
    exact Complex.continuous_conj.comp_aestronglyMeasurable hfi.aestronglyMeasurable
  ·
    have h_finite := hfi.2
    show HasFiniteIntegral _ _
    unfold HasFiniteIntegral at h_finite ⊢
    refine lt_of_le_of_lt (le_of_eq ?_) h_finite
    apply lintegral_congr_ae
    filter_upwards with τ
    show ‖(starRingEnd ℂ) (petersson k f g' τ)‖ₑ = ‖petersson k f g' τ‖ₑ
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    exact Subtype.ext (Complex.norm_conj _)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T205/T128 bridge: GL-pair AE-disjoint on the SL(2, ℤ)-fundamental
domain `ModularGroup.fd` via `mapGL ℝ σ`-factored inverse product**. -/
theorem aedisjoint_glMap_smul_fd_of_mul_inv_eq_mapGL_PSL_ne
    (α₁ α₂ : GL (Fin 2) ℝ)
    (h_mp_inv : MeasurePreserving ((α₁⁻¹ • ·) : ℍ → ℍ) μ_hyp μ_hyp)
    (σ : SL(2, ℤ)) (hσ_ne : (QuotientGroup.mk σ : PSL(2, ℤ)) ≠ 1)
    (h_inv_mul : α₁⁻¹ * α₂ =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) σ : GL (Fin 2) ℝ)) :
    AEDisjoint μ_hyp (α₁ • (ModularGroup.fd : Set UpperHalfPlane))
      (α₂ • (ModularGroup.fd : Set UpperHalfPlane)) := by
  set q : PSL(2, ℤ) := QuotientGroup.mk σ with hq_def
  have h_fdo_aedisjoint : AEDisjoint μ_hyp (fdo : Set ℍ) (q • (fdo : Set ℍ)) := by
    have h_ne : (1 : PSL(2, ℤ)) ≠ q := fun h ↦ hσ_ne h.symm
    have h_gen := isFundamentalDomain_fdo_PSL.aedisjoint h_ne
    simp only [Function.onFun, one_smul] at h_gen
    exact h_gen
  have h_q_smul_aeeq :
      (q • (ModularGroup.fd : Set UpperHalfPlane) : Set ℍ) =ᵐ[μ_hyp] (q • (fdo : Set ℍ)) := by
    refine ae_eq_set.mpr ⟨?_, ?_⟩
    ·
      have h_sdiff : (q • (ModularGroup.fd : Set UpperHalfPlane) \ q • (fdo : Set ℍ) : Set ℍ) =
          q • ((ModularGroup.fd : Set UpperHalfPlane) \ fdo) := by
        ext x
        simp only [Set.mem_diff, Set.mem_smul_set_iff_inv_smul_mem]
      rw [h_sdiff, measure_smul]
      exact hyperbolicMeasure_fd_boundary
    ·
      have h_fdo_sub_fd : q • (fdo : Set ℍ) ⊆ q • (ModularGroup.fd : Set UpperHalfPlane) := by
        intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact ⟨y, fdo_subset_fd hy, rfl⟩
      rw [Set.diff_eq_empty.mpr h_fdo_sub_fd]
      exact measure_empty
  have h_inner : AEDisjoint μ_hyp (ModularGroup.fd : Set UpperHalfPlane)
      (q • (ModularGroup.fd : Set UpperHalfPlane)) :=
    h_fdo_aedisjoint.congr fd_ae_eq_fdo h_q_smul_aeeq
  have h_pre_α₁ : ((α₁⁻¹ • ·) ⁻¹' (ModularGroup.fd : Set UpperHalfPlane) : Set ℍ) =
      α₁ • (ModularGroup.fd : Set UpperHalfPlane) := by
    ext τ; simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  have h_pre_α₂ : ((α₁⁻¹ • ·) ⁻¹' (q • (ModularGroup.fd : Set UpperHalfPlane)) : Set ℍ) =
      α₂ • (ModularGroup.fd : Set UpperHalfPlane) := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
    have hq_smul : ∀ z : ℍ, (q⁻¹ • z : ℍ) =
        (((mapGL ℝ : SL(2, ℤ) →* _) σ)⁻¹ : GL (Fin 2) ℝ) • z := by
      intro z
      rw [hq_def, ← QuotientGroup.mk_inv, PSL_smul_coe]
      rw [sl_moeb, show ((σ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
          ((mapGL ℝ : SL(2, ℤ) →* _) σ)⁻¹ by
        rw [← map_inv]; rfl]
    rw [hq_smul (α₁⁻¹ • τ)]
    have h_eq : ((mapGL ℝ : SL(2, ℤ) →* _) σ)⁻¹ = α₂⁻¹ * α₁ := by
      rw [← h_inv_mul, mul_inv_rev, inv_inv]
    rw [h_eq, mul_smul]
    rw [show (α₁ • α₁⁻¹ • τ : ℍ) = τ by
      rw [← mul_smul, mul_inv_cancel, one_smul]]
  have h_QMP : MeasureTheory.Measure.QuasiMeasurePreserving
      ((α₁⁻¹ • ·) : ℍ → ℍ) μ_hyp μ_hyp :=
    h_mp_inv.quasiMeasurePreserving
  have h_pre_aedisjoint : AEDisjoint μ_hyp
      ((α₁⁻¹ • ·) ⁻¹' (ModularGroup.fd : Set UpperHalfPlane))
      ((α₁⁻¹ • ·) ⁻¹' (q • (ModularGroup.fd : Set UpperHalfPlane))) :=
    h_inner.preimage h_QMP
  rw [h_pre_α₁, h_pre_α₂] at h_pre_aedisjoint
  exact h_pre_aedisjoint

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094 bridge: GL-pair AE-disjoint via `mapGL ℝ γ`-factored inverse product.**

For `α₁, α₂ : GL (Fin 2) ℝ` with `α₁⁻¹` measure-preserving on ℍ, if
`α₁⁻¹ * α₂ = mapGL ℝ γ` for some `γ ∈ Γ₁(N)` non-trivial in `PSL(2,ℤ)`,
then `α₁ • D_N^PSL` and `α₂ • D_N^PSL` are AE-disjoint. -/
theorem aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1
    {N : ℕ} [NeZero N] (α₁ α₂ : GL (Fin 2) ℝ)
    (h_mp_inv : MeasurePreserving ((α₁⁻¹ • ·) : ℍ → ℍ) μ_hyp μ_hyp)
    (γ : SL(2, ℤ)) (hγ_Γ1 : γ ∈ Gamma1 N)
    (hγ_ne : (QuotientGroup.mk γ : PSL(2, ℤ)) ≠ 1)
    (h_inv_mul : α₁⁻¹ * α₂ = ((mapGL ℝ : SL(2, ℤ) →* _) γ : GL (Fin 2) ℝ)) :
    AEDisjoint μ_hyp (α₁ • (Gamma1_fundDomain_PSL N : Set ℍ))
      (α₂ • (Gamma1_fundDomain_PSL N : Set ℍ)) := by
  set D : Set ℍ := Gamma1_fundDomain_PSL N
  set q : PSL(2, ℤ) := QuotientGroup.mk γ with hq_def
  have h_inner : AEDisjoint μ_hyp D (q • D) := by
    have h_mem : (1 : PSL(2, ℤ))⁻¹ * q ∈ imageGamma1_PSL N := by
      rw [inv_one, one_mul, hq_def]
      exact Subgroup.mem_map.mpr ⟨γ, hγ_Γ1, rfl⟩
    have h_ne : (1 : PSL(2, ℤ))⁻¹ * q ≠ 1 := by
      rw [inv_one, one_mul]; exact hγ_ne
    have h_gen := isFundamentalDomain_Gamma1_coset_tiling (N := N)
      |>.aedisjoint_smul_of_mul_inv_mem h_mem h_ne
    rwa [one_smul] at h_gen
  have h_pre_α₁ : ((α₁⁻¹ • ·) ⁻¹' D : Set ℍ) = α₁ • D := by
    ext τ; simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  have h_pre_α₂ : ((α₁⁻¹ • ·) ⁻¹' (q • D) : Set ℍ) = α₂ • D := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
    have hq_smul : ∀ σ : ℍ, (q⁻¹ • σ : ℍ) =
        (((mapGL ℝ : SL(2, ℤ) →* _) γ)⁻¹ : GL (Fin 2) ℝ) • σ := by
      intro σ
      rw [hq_def, ← QuotientGroup.mk_inv, PSL_smul_coe]
      rw [sl_moeb, show ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
          ((mapGL ℝ : SL(2, ℤ) →* _) γ)⁻¹ by
        rw [← map_inv]; rfl]
    rw [hq_smul (α₁⁻¹ • τ)]
    have h_eq : ((mapGL ℝ : SL(2, ℤ) →* _) γ)⁻¹ = α₂⁻¹ * α₁ := by
      rw [← h_inv_mul, mul_inv_rev, inv_inv]
    rw [h_eq, mul_smul]
    rw [show (α₁ • α₁⁻¹ • τ : ℍ) = τ by
      rw [← mul_smul, mul_inv_cancel, one_smul]]
  have h_QMP : MeasureTheory.Measure.QuasiMeasurePreserving
      ((α₁⁻¹ • ·) : ℍ → ℍ) μ_hyp μ_hyp :=
    h_mp_inv.quasiMeasurePreserving
  have h_pre_aedisjoint : AEDisjoint μ_hyp
      ((α₁⁻¹ • ·) ⁻¹' D) ((α₁⁻¹ • ·) ⁻¹' (q • D)) :=
    h_inner.preimage h_QMP
  rw [h_pre_α₁, h_pre_α₂] at h_pre_aedisjoint
  exact h_pre_aedisjoint

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094 matrix identity M1: `T_p_upper` inverse-product factors through
`shiftSL_loc`.**

`(glMap T_p_upper(b₁))⁻¹ * (glMap T_p_upper(b₂)) = mapGL ℝ (shiftSL_loc (b₂ - b₁))`
in `GL (Fin 2) ℝ`. Proved via `A * (shift) = B` computation, inverted. -/
theorem glMap_T_p_upper_inv_mul_eq_mapGL_shift
    {p : ℕ} (hp : 0 < p) (b₁ b₂ : ℕ) :
    (glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ)⁻¹ *
        (glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* _) (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)))) := by
  have h_mul : (glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)))) := by
    apply Units.ext
    ext i j
    have h_L : ((glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b₂ : ℝ); 0, (p : ℝ)] := by
      ext i' j'; fin_cases i' <;> fin_cases j' <;>
        simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.GeneralLinearGroup.map, Matrix.of_apply]
    have h_R1 : ((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b₁ : ℝ); 0, (p : ℝ)] := by
      ext i' j'; fin_cases i' <;> fin_cases j' <;>
        simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.GeneralLinearGroup.map, Matrix.of_apply]
    have h_R2 : (((mapGL ℝ : SL(2, ℤ) →* _) (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)))) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b₂ : ℝ) - (b₁ : ℝ); 0, 1] := by
      ext i' j'; fin_cases i' <;> fin_cases j' <;>
        simp [mapGL_coe_matrix, shiftSL_loc, algebraMap_int_eq, Matrix.of_apply]
    show ((glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) : Matrix _ _ ℝ) i j =
      ((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) *
       ((mapGL ℝ : SL(2, ℤ) →* _) (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)))) :
       GL (Fin 2) ℝ).val i j
    rw [h_L, Units.val_mul, h_R1, h_R2]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;> ring
  rw [h_mul, ← mul_assoc, inv_mul_cancel, one_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094: AE-disjoint for two `T_p_upper`-translates.** -/
theorem aedisjoint_glMap_T_p_upper_pair
    {N : ℕ} [NeZero N] {p : ℕ} (hp : 0 < p) {b₁ b₂ : ℕ}
    (hne : (b₂ : ℤ) - (b₁ : ℤ) ≠ 0) :
    AEDisjoint μ_hyp
      ((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set ℍ))
      ((glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) := by
  have h_det_pos : ∀ b, 0 < (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ).det.val := by
    intro b
    show 0 < ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
      (algebraMap ℚ ℝ) (((T_p_upper p hp b : GL (Fin 2) ℚ).val).det) from
        (RingHom.map_det _ _).symm]
    rw [show ((T_p_upper p hp b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp
  have h_inv_det_pos : 0 <
      ((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ)⁻¹).det.val := by
    have hα_pos := h_det_pos b₁
    show 0 < ((((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ)⁻¹).det : ℝˣ) : ℝ)
    rw [show (((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ)⁻¹).det : ℝˣ) =
        ((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ).det : ℝˣ)⁻¹ from map_inv _ _]
    show 0 < (((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ).det : ℝˣ))⁻¹.val
    rw [Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hα_pos
  have h_psl_ne : (QuotientGroup.mk (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ))) :
      PSL(2, ℤ)) ≠ 1 := by
    intro heq
    rw [QuotientGroup.eq_one_iff] at heq
    have hS : (!![(0 : ℤ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
      simp [Matrix.det_fin_two]
    set S_mat : SL(2, ℤ) := ⟨!![0, -1; 1, 0], hS⟩
    have hcomm : shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) * S_mat =
        S_mat * shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) := heq.comm S_mat
    have hcomm_val :
        (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) : SL(2, ℤ)).val * S_mat.val =
        S_mat.val * (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) : SL(2, ℤ)).val :=
      congr_arg Subtype.val hcomm
    have h_00 := congr_fun (congr_fun hcomm_val 0) 0
    simp only [S_mat, shiftSL_loc, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h_00
    apply hne; linarith
  exact aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1
    (glMap (T_p_upper p hp b₁)) (glMap (T_p_upper p hp b₂))
    (measurePreserving_glPos_smul _ h_inv_det_pos)
    (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ))) (shiftSL_loc_mem_Gamma1 _) h_psl_ne
    (glMap_T_p_upper_inv_mul_eq_mapGL_shift hp b₁ b₂)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T205 per-`q` upper-family pairwise AE-disjoint on `fd`-tiles**:
for fixed `q : SL(2, ℤ)` and `b₁ ≠ b₂`, the tiles
`(glMap T_p_upper(p, b) * mapGL q⁻¹) • fd` are pairwise AE-disjoint. -/
theorem aedisjoint_glMap_T_p_upper_pair_fd_per_q
    {p : ℕ} (hp : 0 < p) (q : SL(2, ℤ)) {b₁ b₂ : ℕ}
    (hne : (b₂ : ℤ) - (b₁ : ℤ) ≠ 0) :
    AEDisjoint μ_hyp
      (((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
      (((glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) := by
  set α₁ : GL (Fin 2) ℝ :=
    (glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)
  set α₂ : GL (Fin 2) ℝ :=
    (glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)
  have h_Tp_det_pos :
      ∀ b, 0 < (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ).det.val := by
    intro b
    show 0 < ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_upper p hp b : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_upper p hp b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp
  have h_mapGL_mat_det_eq_one :
      (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [show (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix (q⁻¹ : SL(2, ℤ)).val) by
      rw [mapGL_coe_matrix]; rfl]
    rw [← RingHom.map_det, (q⁻¹ : SL(2, ℤ)).property]
    simp
  have h_α₁_det_pos : 0 < (α₁ : GL (Fin 2) ℝ).det.val := by
    show 0 < ((α₁ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((α₁ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) from Units.val_mul _ _,
      Matrix.det_mul, h_mapGL_mat_det_eq_one, mul_one]
    exact h_Tp_det_pos b₁
  have h_α₁_inv_det_pos : 0 < (α₁⁻¹ : GL (Fin 2) ℝ).det.val := by
    show 0 < (((α₁⁻¹).det : ℝˣ) : ℝ)
    rw [show ((α₁⁻¹ : GL (Fin 2) ℝ)).det = α₁.det⁻¹ from map_inv _ _,
      Units.val_inv_eq_inv_val]
    exact inv_pos.mpr h_α₁_det_pos
  have h_inv_mul : α₁⁻¹ * α₂ =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q * shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) * q⁻¹) : GL (Fin 2) ℝ) := by
    show (((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ))⁻¹ *
        ((glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ))) = _
    rw [mul_inv_rev]
    rw [show (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ))⁻¹ =
          ((mapGL ℝ : SL(2, ℤ) →* _) q : GL (Fin 2) ℝ) by
        rw [← map_inv]; simp]
    rw [mul_assoc ((mapGL ℝ : SL(2, ℤ) →* _) q : GL (Fin 2) ℝ)
          (glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ)⁻¹,
      ← mul_assoc ((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ)⁻¹)
          (glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ)
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ),
      glMap_T_p_upper_inv_mul_eq_mapGL_shift hp b₁ b₂,
      ← mul_assoc]
    rw [← map_mul, ← map_mul]
  have h_psl_shift_ne :
      (QuotientGroup.mk (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ))) :
        PSL(2, ℤ)) ≠ 1 := by
    intro heq
    rw [QuotientGroup.eq_one_iff] at heq
    have hS : (!![(0 : ℤ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
      simp [Matrix.det_fin_two]
    set S_mat : SL(2, ℤ) := ⟨!![0, -1; 1, 0], hS⟩
    have hcomm : shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) * S_mat =
        S_mat * shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) := heq.comm S_mat
    have hcomm_val :
        (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) : SL(2, ℤ)).val * S_mat.val =
        S_mat.val * (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) : SL(2, ℤ)).val :=
      congr_arg Subtype.val hcomm
    have h_00 := congr_fun (congr_fun hcomm_val 0) 0
    simp only [S_mat, shiftSL_loc, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h_00
    apply hne; linarith
  have h_psl_conj_ne :
      (QuotientGroup.mk (q * shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) * q⁻¹) :
        PSL(2, ℤ)) ≠ 1 := by
    intro heq
    apply h_psl_shift_ne
    have hconj : (QuotientGroup.mk q : PSL(2, ℤ)) *
            (QuotientGroup.mk (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ))) : PSL(2, ℤ)) *
            (QuotientGroup.mk q : PSL(2, ℤ))⁻¹ = 1 := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact heq
    rw [mul_inv_eq_one] at hconj
    exact mul_left_cancel (hconj.trans (mul_one _).symm)
  exact aedisjoint_glMap_smul_fd_of_mul_inv_eq_mapGL_PSL_ne α₁ α₂
    (measurePreserving_glPos_smul _ h_α₁_inv_det_pos)
    (q * shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)) * q⁻¹)
    h_psl_conj_ne h_inv_mul

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T205 per-`q` upper-family union-collapse (peterssonInner form)**. -/
theorem peterssonInner_T_p_upper_family_union_collapse_per_q
    {p : ℕ} [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfi : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp) :
    ∑ b ∈ Finset.range p,
      peterssonInner k
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
    peterssonInner k
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
      ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  have h_fd_mset : MeasurableSet (ModularGroup.fd : Set UpperHalfPlane) :=
    ((isClosed_le continuous_const
        (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)).inter
      (isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re)
        continuous_const)).measurableSet
  have h_fd_null : NullMeasurableSet (ModularGroup.fd : Set UpperHalfPlane) μ_hyp :=
    h_fd_mset.nullMeasurableSet
  have h_Tp_det_pos :
      ∀ b, 0 < (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ).det.val := by
    intro b
    show 0 < ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp.pos
  have h_mapGL_mat_det_eq_one :
      (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [show (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix (q⁻¹ : SL(2, ℤ)).val) by
      rw [mapGL_coe_matrix]; rfl]
    rw [← RingHom.map_det, (q⁻¹ : SL(2, ℤ)).property]
    simp
  have h_α_det_pos : ∀ b, 0 <
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)).det.val := fun b ↦ by
    show 0 < (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)) :
          Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)) :
            Matrix (Fin 2) (Fin 2) ℝ) =
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) from Units.val_mul _ _,
      Matrix.det_mul, h_mapGL_mat_det_eq_one, mul_one]
    exact h_Tp_det_pos b
  have h_α_inv_det_pos : ∀ b, 0 <
      (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ))⁻¹ :
          GL (Fin 2) ℝ).det.val := fun b ↦ by
    have hα_pos := h_α_det_pos b
    show 0 < (((((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ))⁻¹).det : ℝˣ) : ℝ)
    rw [show (((((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ))⁻¹).det : ℝˣ)) =
        ((((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)).det : ℝˣ))⁻¹ from
          map_inv _ _]
    show 0 < ((((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)).det : ℝˣ))⁻¹.val
    rw [Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hα_pos
  have hm : ∀ b ∈ Finset.range p, NullMeasurableSet
      (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp := fun b _ ↦ by
    have h_eq : (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane)) =
        (((((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ))⁻¹ • ·) :
              ℍ → ℍ) ⁻¹' (ModularGroup.fd : Set UpperHalfPlane)) := by
      ext τ; simp [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
    rw [h_eq]
    exact h_fd_null.preimage
      (measurePreserving_glPos_smul _ (h_α_inv_det_pos b)).quasiMeasurePreserving
  have hd : (↑(Finset.range p) : Set ℕ).Pairwise fun b₁ b₂ ↦ AEDisjoint μ_hyp
        (((glMap (T_p_upper p hp.pos b₁) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
        (((glMap (T_p_upper p hp.pos b₂) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane)) := fun b₁ _ b₂ _ hne ↦ by
    apply aedisjoint_glMap_T_p_upper_pair_fd_per_q hp.pos q
    intro h
    apply hne
    exact_mod_cast (sub_eq_zero.mp h).symm
  exact (peterssonInner_biUnion_finset_ae (Finset.range p) hm hd ⇑f _ hfi).symm

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094: `μ_hyp` is invariant under positive-det `GL (Fin 2) ℝ` translates.**

Uses the `(α⁻¹ • ·)` preimage formula and `MeasurePreserving.measure_preimage` on
the GL(2, ℝ)⁺ lift. -/
theorem measure_glPos_smul_eq (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    {S : Set ℍ} (hS : NullMeasurableSet S μ_hyp) :
    μ_hyp (α • S) = μ_hyp S := by
  have hα_inv : 0 < (α⁻¹ : GL (Fin 2) ℝ).det.val := by
    show 0 < (((α⁻¹).det : ℝˣ) : ℝ)
    rw [show ((α⁻¹ : GL (Fin 2) ℝ)).det = α.det⁻¹ from map_inv _ _,
      Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hα
  have h_mp_inv := measurePreserving_glPos_smul α⁻¹ hα_inv
  have h_eq : ((α⁻¹ • ·) : ℍ → ℍ) ⁻¹' S = α • S := by
    ext τ; simp [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  rw [← h_eq]
  exact h_mp_inv.measure_preimage hS

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094: finite hyperbolic measure of a `glMap`-translate of the Γ₁(N)-FD.** -/
theorem measure_glPos_smul_Gamma1_fundDomain_lt_top
    {N : ℕ} [NeZero N] (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val) :
    μ_hyp (α • (Gamma1_fundDomain_PSL N : Set ℍ)) < ⊤ := by
  rw [measure_glPos_smul_eq α hα
    isFundamentalDomain_Gamma1_PSL.nullMeasurableSet]
  exact hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094: Petersson integrand integrable on a single `glMap`-translate of
`Gamma1_fundDomain_PSL N`.** -/
theorem integrableOn_petersson_glMap_smul_Gamma1_fundDomain
    {N : ℕ} [NeZero N] (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IntegrableOn (fun τ ↦ petersson k ⇑f ⇑g τ)
      (α • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f g
  exact IntegrableOn.of_bound (measure_glPos_smul_Gamma1_fundDomain_lt_top α hα)
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous g)).aestronglyMeasurable.restrict)
    C (ae_of_all _ fun τ ↦ hC τ)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094: Petersson integrand integrable on a `Finset`-biUnion of
positive-det `glMap`-translates.** -/
theorem integrableOn_petersson_biUnion_glMap_smul
    {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι) (α : ι → GL (Fin 2) ℝ)
    (hα : ∀ i ∈ s, 0 < (α i).det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
  IntegrableOn (fun τ ↦ petersson k ⇑f ⇑g τ)
      (⋃ i ∈ s, α i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f g
  have h_finite : μ_hyp (⋃ i ∈ s, α i • (Gamma1_fundDomain_PSL N : Set ℍ)) < ⊤ := by
    refine lt_of_le_of_lt (measure_biUnion_finset_le s _) ?_
    refine ENNReal.sum_lt_top.mpr fun i hi ↦ ?_
    exact measure_glPos_smul_Gamma1_fundDomain_lt_top (α i) (hα i hi)
  exact IntegrableOn.of_bound h_finite
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous g)).aestronglyMeasurable.restrict)
    C (ae_of_all _ fun τ ↦ hC τ)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094: pairwise AE-disjoint finite family, parametrized by per-pair
hypotheses.** -/
theorem aedisjoint_pairwise_family_of_pair_ae_disjoint
    {ι : Type*} {D : Set ℍ} (s : Finset ι) (α : ι → GL (Fin 2) ℝ)
    (h_pair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      AEDisjoint μ_hyp (α i • D) (α j • D)) :
    (↑s : Set ι).Pairwise (fun i j ↦ AEDisjoint μ_hyp (α i • D) (α j • D)) :=
  fun i hi j hj hij ↦ h_pair i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hij

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094 matrix identity M2 witness: explicit Γ₁(N) factor from
`T_p_upper(b)⁻¹ · M_∞`.**

SL(2, ℤ) element with matrix `!![ap − bNm, 1 − b; Nm, 1]`
(where `a = aInvOfCoprime, m = mIdxOfCoprime`, so `ap − Nm = 1` by Bezout). -/
noncomputable def M_infty_Gamma1_factor
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (b : ℕ) : SL(2, ℤ) :=
  ⟨!![(aInvOfCoprime N p hpN : ℤ) * p - (b : ℤ) * ((N : ℤ) * mIdxOfCoprime N p hpN),
      1 - (b : ℤ);
      (N : ℤ) * mIdxOfCoprime N p hpN, 1],
    by
      have h := N_mul_mIdx_eq N p hpN
      rw [Matrix.det_fin_two_of]; linarith⟩

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094: `M_infty_Gamma1_factor` lies in `Γ₁(N)`.** -/
theorem M_infty_Gamma1_factor_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (b : ℕ) :
    M_infty_Gamma1_factor N p hpN b ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have hN : (((N : ℤ) : ZMod N) : ZMod N) = 0 := by
    push_cast; exact ZMod.natCast_self N
  refine ⟨?_, ?_, ?_⟩
  ·
    change ((((aInvOfCoprime N p hpN : ℤ) * p -
        (b : ℤ) * ((N : ℤ) * mIdxOfCoprime N p hpN)) : ℤ) : ZMod N) = 1
    push_cast
    have : (((b : ℕ) : ZMod N) *
        (((N : ℕ) : ZMod N) * ((mIdxOfCoprime N p hpN : ℤ) : ZMod N))) = 0 := by
      rw [show (((N : ℕ) : ZMod N)) = 0 from ZMod.natCast_self N]; ring
    rw [this, sub_zero]
    exact aInvOfCoprime_mul_eq_one N p hpN
  · change ((1 : ℤ) : ZMod N) = 1
    push_cast; rfl
  · change ((((N : ℤ) * mIdxOfCoprime N p hpN) : ℤ) : ZMod N) = 0
    push_cast
    rw [show (((N : ℕ) : ZMod N)) = 0 from ZMod.natCast_self N]; ring

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094: `M_infty_Gamma1_factor` is non-trivial in `PSL(2, ℤ)` for `p` prime.** -/
theorem M_infty_Gamma1_factor_psl_ne_one
    (N p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ) :
    (QuotientGroup.mk (M_infty_Gamma1_factor N p hpN b) : PSL(2, ℤ)) ≠ 1 := by
  intro heq
  rw [QuotientGroup.eq_one_iff] at heq
  have hS : (!![(0 : ℤ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [Matrix.det_fin_two]
  set S_mat : SL(2, ℤ) := ⟨!![0, -1; 1, 0], hS⟩
  have hcomm : M_infty_Gamma1_factor N p hpN b * S_mat =
      S_mat * M_infty_Gamma1_factor N p hpN b := heq.comm S_mat
  have hcomm_val : (M_infty_Gamma1_factor N p hpN b : SL(2, ℤ)).val * S_mat.val =
      S_mat.val * (M_infty_Gamma1_factor N p hpN b : SL(2, ℤ)).val :=
    congr_arg Subtype.val hcomm
  have h_10 := congr_fun (congr_fun hcomm_val 1) 0
  simp only [S_mat, M_infty_Gamma1_factor, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h_10
  have h_00 := congr_fun (congr_fun hcomm_val 0) 0
  simp only [S_mat, M_infty_Gamma1_factor, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h_00
  have h_bezout := N_mul_mIdx_eq N p hpN
  have h_Nm_zero : (N : ℤ) * mIdxOfCoprime N p hpN = 0 := by
    have h_sub : (1 - (b : ℤ)) * ((N : ℤ) * mIdxOfCoprime N p hpN) = 0 := by
      linarith
    have h_subst : -((N : ℤ) * mIdxOfCoprime N p hpN) *
        ((N : ℤ) * mIdxOfCoprime N p hpN) = 0 := by
      have : (1 - (b : ℤ)) = -((N : ℤ) * mIdxOfCoprime N p hpN) := by linarith
      rw [this] at h_sub; exact h_sub
    have h_sq : ((N : ℤ) * mIdxOfCoprime N p hpN)^2 = 0 := by
      have := h_subst; nlinarith
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_sq
  have h_ap : (aInvOfCoprime N p hpN : ℤ) * p = 1 := by linarith
  have hp_div : (p : ℤ) ∣ 1 := ⟨aInvOfCoprime N p hpN, by linarith⟩
  have hp_ge : (p : ℤ) ≥ 2 := by exact_mod_cast hp.two_le
  have hp_unit := Int.isUnit_iff.mp (isUnit_of_dvd_one hp_div)
  rcases hp_unit with h | h <;> omega

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094 matrix identity M2: `(T_p_upper(b))⁻¹ · M_∞ = mapGL ℝ
(M_infty_Gamma1_factor)`.**  Verified via `M_∞ = T_p_upper(b) · γ'` computation. -/
theorem glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (b : ℕ) :
    (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)⁻¹ *
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN b)) := by
  have h_mul : (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN b)) := by
    apply Units.ext
    ext i j
    have h_L : ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        !![((aInvOfCoprime N p hpN : ℤ) : ℝ) * (p : ℝ), 1;
           (((N : ℤ) * mIdxOfCoprime N p hpN : ℤ) : ℝ) * (p : ℝ), (p : ℝ)] := by
      ext i' j'; fin_cases i' <;> fin_cases j' <;>
        simp [glMap, M_infty, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.GeneralLinearGroup.map, Matrix.of_apply]
    have h_R1 : ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] := by
      ext i' j'; fin_cases i' <;> fin_cases j' <;>
        simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.GeneralLinearGroup.map, Matrix.of_apply]
    have h_R2 : (((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN b)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        !![((aInvOfCoprime N p hpN : ℤ) : ℝ) * (p : ℝ) -
             (b : ℝ) * (((N : ℤ) * mIdxOfCoprime N p hpN : ℤ) : ℝ),
           (1 : ℝ) - (b : ℝ);
           (((N : ℤ) * mIdxOfCoprime N p hpN : ℤ) : ℝ), 1] := by
      ext i' j'; fin_cases i' <;> fin_cases j' <;>
        simp [mapGL_coe_matrix, M_infty_Gamma1_factor, algebraMap_int_eq,
          Matrix.of_apply]
    show ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) : Matrix _ _ ℝ) i j =
      ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) *
       ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN b)) :
       GL (Fin 2) ℝ).val i j
    rw [h_L, Units.val_mul, h_R1, h_R2]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;> ring
  rw [h_mul, ← mul_assoc, inv_mul_cancel, one_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094: AE-disjoint for `T_p_upper(b)` vs `M_∞` (p prime).** -/
theorem aedisjoint_glMap_M_infty_T_p_upper
    {N : ℕ} [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ) :
    AEDisjoint μ_hyp
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set ℍ))
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) := by
  have h_det_pos : 0 < (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ).det.val := by
    show 0 < ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
      (algebraMap ℚ ℝ) (((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).det) from
        (RingHom.map_det _ _).symm]
    rw [show ((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp.pos
  have h_inv_det_pos : 0 <
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)⁻¹).det.val := by
    show 0 < ((((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)⁻¹).det : ℝˣ) : ℝ)
    rw [show (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)⁻¹).det : ℝˣ) =
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ).det : ℝˣ)⁻¹ from
      map_inv _ _]
    show 0 < (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ).det : ℝˣ))⁻¹.val
    rw [Units.val_inv_eq_inv_val]
    exact inv_pos.mpr h_det_pos
  exact aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1
    (glMap (T_p_upper p hp.pos b)) (glMap (M_infty N p hp.pos hpN))
    (measurePreserving_glPos_smul _ h_inv_det_pos)
    (M_infty_Gamma1_factor N p hpN b)
    (M_infty_Gamma1_factor_mem_Gamma1 N p hpN b)
    (M_infty_Gamma1_factor_psl_ne_one N p hp hpN b)
    (glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp.pos hpN b)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T094: T_p-double-coset family `{T_p_upper(b)}_{b<p} ∪ {M_∞}` — pairwise
AE-disjoint translates of `Gamma1_fundDomain_PSL N`.** -/
theorem aedisjoint_pairwise_T_p_family
    {N : ℕ} [NeZero N] (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    (↑(Finset.univ : Finset (Option (Fin p))) : Set (Option (Fin p))).Pairwise
      (fun i j ↦ AEDisjoint μ_hyp
          ((match i with
            | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
              (Gamma1_fundDomain_PSL N : Set ℍ))
          ((match j with
            | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
              (Gamma1_fundDomain_PSL N : Set ℍ))) := by
  intro i _ j _ hij
  match i, j, hij with
  | none, none, h => exact absurd rfl h
  | none, some b, _ =>
    exact (aedisjoint_glMap_M_infty_T_p_upper hp hpN b.val).symm
  | some b, none, _ => exact aedisjoint_glMap_M_infty_T_p_upper hp hpN b.val
  | some b₁, some b₂, hij =>
    refine aedisjoint_glMap_T_p_upper_pair hp.pos ?_
    intro h_eq
    apply hij
    have h_val : b₁.val = b₂.val := by
      have : (b₁.val : ℤ) = (b₂.val : ℤ) := by linarith
      exact_mod_cast this
    exact congr_arg some (Fin.ext h_val)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T090 / T205 reusable: Petersson sum-of-slashes ↔ aggregate Hecke-FD biUnion
for a finite family of GL(2,ℝ)⁺ representatives with a common adjoint cusp form.** -/
theorem peterssonInner_T_p_family_sum_slashes_eq_aggregate
    {N : ℕ} [NeZero N] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ) (hα : ∀ i ∈ s, 0 < (α i).det.val)
    (f g g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hadj : ∀ i ∈ s, ⇑g ∣[k] peterssonAdj (α i) = ⇑g')
    (hm : ∀ i ∈ s,
      NullMeasurableSet (α i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (hd : (↑s : Set ι).Pairwise
      (fun i j ↦ AEDisjoint μ_hyp
        (α i • (Gamma1_fundDomain_PSL N : Set ℍ))
        (α j • (Gamma1_fundDomain_PSL N : Set ℍ))))
    (h_int_per : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k ⇑g (⇑f ∣[k] α i) τ)
        (Gamma1_fundDomain_PSL N) μ_hyp) :
    peterssonInner k (Gamma1_fundDomain_PSL N) (∑ i ∈ s, ⇑f ∣[k] α i) ⇑g =
      peterssonInner k
        (⋃ i ∈ s, α i • (Gamma1_fundDomain_PSL N : Set ℍ))
        ⇑f ⇑g' :=
  peterssonInner_sum_slash_adjoint_constantRHS s α hα
    (Gamma1_fundDomain_PSL N) ⇑f ⇑g ⇑g' hadj h_int_per hm hd
    (integrableOn_petersson_biUnion_glMap_smul s α hα f g')

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T090 / T205 reusable: Petersson sum-of-slashes ↔ aggregate Hecke-FD biUnion
with explicit union-integrability hypothesis (companion to
`peterssonInner_T_p_family_sum_slashes_eq_aggregate`).** -/
theorem peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable
    {N : ℕ} [NeZero N] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ) (hα : ∀ i ∈ s, 0 < (α i).det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g' : ℍ → ℂ)
    (hadj : ∀ i ∈ s, ⇑g ∣[k] peterssonAdj (α i) = g')
    (hm : ∀ i ∈ s,
      NullMeasurableSet (α i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (hd : (↑s : Set ι).Pairwise
      (fun i j ↦ AEDisjoint μ_hyp
        (α i • (Gamma1_fundDomain_PSL N : Set ℍ))
        (α j • (Gamma1_fundDomain_PSL N : Set ℍ))))
    (h_int_per : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k ⇑g (⇑f ∣[k] α i) τ)
        (Gamma1_fundDomain_PSL N) μ_hyp)
    (hfi : IntegrableOn (fun τ ↦ petersson k ⇑f g' τ)
      (⋃ i ∈ s, α i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp) :
    peterssonInner k (Gamma1_fundDomain_PSL N) (∑ i ∈ s, ⇑f ∣[k] α i) ⇑g =
      peterssonInner k
        (⋃ i ∈ s, α i • (Gamma1_fundDomain_PSL N : Set ℍ))
        ⇑f g' :=
  peterssonInner_sum_slash_adjoint_constantRHS s α hα
    (Gamma1_fundDomain_PSL N) ⇑f ⇑g g' hadj h_int_per hm hd hfi

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_slash_adjoint_coset_right
    (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val) (q : SL(2, ℤ)) (f g : ℍ → ℂ) :
    peterssonInner k fd
        (f ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ))
        (g ∣[k] (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ))) =
      peterssonInner k
        (β • ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)))
        (f ∣[k] peterssonAdj β)
        g := by
  have h1 := peterssonInner_conj_symm k fd (f ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ))
      (g ∣[k] (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)))
  have h2 := peterssonInner_slash_adjoint_coset (k := k) β hβ q g f
  have h3 := peterssonInner_conj_symm k
      (β • ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)))
      (f ∣[k] peterssonAdj β) g
  rw [← h1, h2, h3]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T024 aggregate per-α slash-adjoint at the Γ₁(N)-FD level**. -/
theorem peterssonInner_sum_slash_adjoint_coset_aggregate
    (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val)
    (F G : UpperHalfPlane → ℂ)
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        ((β * (mapGL ℝ (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        ((β * (mapGL ℝ (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        ((β * (mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint : IntegrableOn (fun τ ↦ petersson k F (G ∣[k] peterssonAdj β) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (β * (mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (F ∣[k] (β * (mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (G ∣[k] (mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (β * (mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
      F (G ∣[k] peterssonAdj β) := by
  rw [show (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
          (F ∣[k] (β * (mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (G ∣[k] (mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k
          ((β * (mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
          F (G ∣[k] peterssonAdj β) by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [peterssonInner_slash_adjoint_coset (k := k) β hβ
      (q.out : SL(2, ℤ)) F G, ← mul_smul]]
  exact (peterssonInner_iUnion_finite_aedisjoint
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ (β * (mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
    hm hd F (G ∣[k] peterssonAdj β) hint).symm

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T106 helper: `glMap M_∞` has positive determinant `p` in `GL (Fin 2) ℝ`.** -/
theorem glMap_M_infty_det_pos
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    0 < (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ).det.val := by
  show 0 < ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ).det
  rw [show ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((M_infty N p hp hpN : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
  rw [show (((M_infty N p hp hpN : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
    (algebraMap ℚ ℝ) (((M_infty N p hp hpN : GL (Fin 2) ℚ).val).det) from
      (RingHom.map_det _ _).symm]
  have h_det_Q : ((M_infty N p hp hpN : GL (Fin 2) ℚ).val).det = (p : ℚ) := by
    have hmem := N_mul_mIdx_eq N p hpN
    simp only [M_infty_val, Matrix.det_fin_two_of]
    have hmem_q : ((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) =
        (aInvOfCoprime N p hpN : ℤ) * p - 1 := by exact_mod_cast hmem
    rw [hmem_q]
    ring
  rw [h_det_Q]
  show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
  rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
  exact_mod_cast hp

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem nullMeasurableSet_M_infty_q_tile
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    NullMeasurableSet
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ))) μ_hyp := by
  have h_fd_null : NullMeasurableSet (ModularGroup.fd : Set ℍ) μ_hyp :=
    ((isClosed_le continuous_const
        (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)).inter
      (isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re)
        continuous_const)).measurableSet.nullMeasurableSet
  set α : GL (Fin 2) ℝ := (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) ((q.out : SL(2, ℤ))⁻¹) :
      GL (Fin 2) ℝ) with hα_def
  have hα_det : 0 < α.det.val := by
    show 0 < (α : GL (Fin 2) ℝ).val.det
    rw [hα_def, Units.val_mul, Matrix.det_mul]
    have h_M_pos := glMap_M_infty_det_pos N p hp.pos hpN
    have h_q_pos : 0 < ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ).det.val := by
      show 0 < ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ).det
      rw [show ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) :
            Matrix (Fin 2) (Fin 2) ℝ) =
          ((Int.castRingHom ℝ).mapMatrix ((q.out : SL(2, ℤ))⁻¹).val) by
        rw [mapGL_coe_matrix]; rfl]
      rw [← RingHom.map_det, ((q.out : SL(2, ℤ))⁻¹).property]; norm_num
    exact mul_pos h_M_pos h_q_pos
  have hα_inv_det : 0 < (α⁻¹ : GL (Fin 2) ℝ).det.val := by
    show 0 < (((α⁻¹).det : ℝˣ) : ℝ)
    rw [show ((α⁻¹ : GL (Fin 2) ℝ)).det = α.det⁻¹ from map_inv _ _,
      Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hα_det
  have h_nested : ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ))) =
      α • (ModularGroup.fd : Set ℍ) := by
    rw [hα_def, mul_smul]
  rw [h_nested]
  have h_eq : (α • (ModularGroup.fd : Set ℍ)) =
      ((α⁻¹ • ·) : ℍ → ℍ) ⁻¹' (ModularGroup.fd : Set ℍ) := by
    ext τ; simp [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  rw [h_eq]
  exact h_fd_null.preimage
    (measurePreserving_glPos_smul _ hα_inv_det).quasiMeasurePreserving

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T128 per-`q` M_∞ vs T_p_upper(b) fd-AE-disjoint helper**. -/
theorem aedisjoint_glMap_M_infty_T_p_upper_fd_per_q
    {N : ℕ} [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (b : ℕ) :
    AEDisjoint μ_hyp
      (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set ℍ))
      (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set ℍ)) := by
  set α₁ : GL (Fin 2) ℝ :=
    (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)
  set α₂ : GL (Fin 2) ℝ :=
    (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)
  have h_mapGL_mat_det_eq_one :
      (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [show (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix (q⁻¹ : SL(2, ℤ)).val) by
      rw [mapGL_coe_matrix]; rfl]
    rw [← RingHom.map_det, (q⁻¹ : SL(2, ℤ)).property]
    simp
  have h_α₁_det_pos : 0 < (α₁ : GL (Fin 2) ℝ).det.val := by
    show 0 < ((α₁ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((α₁ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) from Units.val_mul _ _,
      Matrix.det_mul, h_mapGL_mat_det_eq_one, mul_one]
    exact glMap_M_infty_det_pos N p hp.pos hpN
  have h_α₁_inv_det_pos : 0 < (α₁⁻¹ : GL (Fin 2) ℝ).det.val := by
    show 0 < (((α₁⁻¹).det : ℝˣ) : ℝ)
    rw [show ((α₁⁻¹ : GL (Fin 2) ℝ)).det = α₁.det⁻¹ from map_inv _ _,
      Units.val_inv_eq_inv_val]
    exact inv_pos.mpr h_α₁_det_pos
  have h_inv_mul : α₁⁻¹ * α₂ =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q * (M_infty_Gamma1_factor N p hpN b)⁻¹ * q⁻¹) : GL (Fin 2) ℝ) := by
    show (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ))⁻¹ *
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ))) = _
    rw [mul_inv_rev]
    rw [show (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ))⁻¹ =
          ((mapGL ℝ : SL(2, ℤ) →* _) q : GL (Fin 2) ℝ) by
        rw [← map_inv]; simp]
    have h_inv_mul_M_infty :
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))⁻¹ *
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) =
        ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN b))⁻¹ := by
      have h :=
        glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp.pos hpN b
      rw [show ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN b))⁻¹ =
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)⁻¹ *
            (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))⁻¹ by rw [h]]
      rw [mul_inv_rev, inv_inv]
    rw [mul_assoc ((mapGL ℝ : SL(2, ℤ) →* _) q : GL (Fin 2) ℝ)
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)⁻¹,
      ← mul_assoc ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))⁻¹
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ),
      h_inv_mul_M_infty,
      ← mul_assoc,
      ← map_inv, ← map_mul, ← map_mul]
  have h_psl_factor_ne :
      (QuotientGroup.mk (M_infty_Gamma1_factor N p hpN b) : PSL(2, ℤ)) ≠ 1 :=
    M_infty_Gamma1_factor_psl_ne_one N p hp hpN b
  have h_psl_factor_inv_ne :
      (QuotientGroup.mk (M_infty_Gamma1_factor N p hpN b)⁻¹ : PSL(2, ℤ)) ≠ 1 := by
    intro heq
    apply h_psl_factor_ne
    rw [QuotientGroup.mk_inv] at heq
    exact inv_eq_one.mp heq
  have h_psl_conj_ne :
      (QuotientGroup.mk (q * (M_infty_Gamma1_factor N p hpN b)⁻¹ * q⁻¹) :
        PSL(2, ℤ)) ≠ 1 := by
    intro heq
    apply h_psl_factor_inv_ne
    have hconj : (QuotientGroup.mk q : PSL(2, ℤ)) *
            (QuotientGroup.mk (M_infty_Gamma1_factor N p hpN b)⁻¹ : PSL(2, ℤ)) *
            (QuotientGroup.mk q : PSL(2, ℤ))⁻¹ = 1 := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact heq
    rw [mul_inv_eq_one] at hconj
    exact mul_left_cancel (hconj.trans (mul_one _).symm)
  exact aedisjoint_glMap_smul_fd_of_mul_inv_eq_mapGL_PSL_ne α₁ α₂
    (measurePreserving_glPos_smul _ h_α₁_inv_det_pos)
    (q * (M_infty_Gamma1_factor N p hpN b)⁻¹ * q⁻¹)
    h_psl_conj_ne h_inv_mul

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T106 right-slash M_∞ adjoint coset identity**: per-`q` M_∞-summand
transformation for the Hecke adjoint. -/
theorem peterssonInner_M_infty_slash_adjoint_coset
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : ℍ → ℂ) :
    peterssonInner k fd
        (f ∣[k] ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) *
          (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)))
        (g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) =
      peterssonInner k
        ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)))
        f
        (g ∣[k] ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) (sigma_p_specific N p hp hpN)⁻¹))) := by
  rw [peterssonInner_slash_adjoint_coset
      (glMap (M_infty N p hp hpN)) (glMap_M_infty_det_pos N p hp hpN) q f g]
  rw [peterssonAdj_glMap_M_infty_eq N p hp hpN]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T126 coset-reindex helper (cusp-form version)**: for a `Γ₁(N)`-cusp
form `g` and `γ ∈ Γ₀(N)`, slashing by `(σ q).out⁻¹` where
`σ = Gamma1QuotEquivOfGamma0 γ` equals slashing by `q.out⁻¹` after applying
the diamond operator `⟨Gamma0MapUnits γ⟩`. -/
theorem slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv
    (γ : ↥(Gamma0 N)) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ⇑g ∣[k] ((Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property q).out :
      SL(2, ℤ))⁻¹ =
    ⇑(diamondOp_cusp k (Gamma0MapUnits γ) g) ∣[k]
      (q.out : SL(2, ℤ))⁻¹ := by
  set σ := Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property
  have h_coset_eq : (σ q) = ⟦q.out * (γ : SL(2, ℤ))⁻¹⟧ := by
    conv_lhs => rw [show q = ⟦q.out⟧ from q.out_eq.symm]
    rfl
  have h_out_eq_mk : ⟦(σ q).out⟧ = (⟦q.out * (γ : SL(2, ℤ))⁻¹⟧ :
      SL(2, ℤ) ⧸ Gamma1 N) := by
    rw [← h_coset_eq, (σ q).out_eq]
  have h_mem : ((σ q).out)⁻¹ * (q.out * (γ : SL(2, ℤ))⁻¹) ∈ Gamma1 N := by
    have h_left_rel := Quotient.exact h_out_eq_mk
    change (QuotientGroup.leftRel _).r _ _ at h_left_rel
    rwa [QuotientGroup.leftRel_apply] at h_left_rel
  set η₀ := ((σ q).out)⁻¹ * (q.out * (γ : SL(2, ℤ))⁻¹)
  have h_inv_eq : ((σ q).out : SL(2, ℤ))⁻¹ =
      η₀ * (γ : SL(2, ℤ)) * ((q.out : SL(2, ℤ)))⁻¹ := by
    show ((σ q).out)⁻¹ = η₀ * (γ : SL(2, ℤ)) * (q.out)⁻¹
    show ((σ q).out)⁻¹ = (((σ q).out)⁻¹ * (q.out * (γ : SL(2, ℤ))⁻¹)) *
        (γ : SL(2, ℤ)) * (q.out)⁻¹
    group
  rw [h_inv_eq, SlashAction.slash_mul, SlashAction.slash_mul]
  rw [show ⇑g ∣[k] η₀ = ⇑g from
    SlashInvariantFormClass.slash_action_eq g _
      (Subgroup.mem_map.mpr ⟨η₀, h_mem, rfl⟩)]
  rw [show ⇑g ∣[k] (γ : SL(2, ℤ)) =
    ⇑(diamondOp_cusp k (Gamma0MapUnits γ) g) by
    show ⇑g ∣[k] (mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = _
    show ⇑g ∣[k] (mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ⇑(diamondOpCusp k (Gamma0MapUnits γ) g)
    rw [diamondOpCusp_eq k (Gamma0MapUnits γ) γ rfl]
    rfl]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T128 Hecke-diamond whole-cusp-form coset-reindex helper**: for a
`Γ₁(N)`-cusp form `g` and `γ ∈ Γ₀(N)`, slashing the full `T_p`-image
`heckeT_p_cusp k p hp hpN g` by `(σ q).out⁻¹` (where
`σ = Gamma1QuotEquivOfGamma0 γ`) equals slashing
`heckeT_p_cusp k p hp hpN (⟨Gamma0MapUnits γ⟩ g)` by `q.out⁻¹`. -/
theorem slash_heckeT_p_cusp_Gamma1QuotEquiv_out_inv_eq
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (γ : ↥(Gamma0 N)) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ⇑(heckeT_p_cusp k p hp hpN g) ∣[k]
      ((Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property q).out :
        SL(2, ℤ))⁻¹ =
    ⇑(heckeT_p_cusp k p hp hpN
        (diamondOp_cusp k (Gamma0MapUnits γ) g)) ∣[k]
      (q.out : SL(2, ℤ))⁻¹ := by
  rw [slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv γ
      (heckeT_p_cusp k p hp hpN g) q]
  set d := Gamma0MapUnits γ with hd_def
  suffices h_eq : (⇑(diamondOp_cusp k d (heckeT_p_cusp k p hp hpN g)) :
      UpperHalfPlane → ℂ) =
      ⇑(heckeT_p_cusp k p hp hpN (diamondOp_cusp k d g)) by
    rw [h_eq]
  have h_diamond_cusp_coe : ∀ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      (⇑(diamondOp_cusp k d f) : UpperHalfPlane → ℂ) =
      (⇑f : UpperHalfPlane → ℂ) ∣[k]
        (mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) := fun f ↦ by
    show (⇑(diamondOpCusp k d f) : UpperHalfPlane → ℂ) = _
    rw [diamondOpCusp_eq k d γ rfl]
    rfl
  have h_diamond_mf_coe : ∀ (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      (⇑(diamondOp k d F) : UpperHalfPlane → ℂ) =
      (⇑F : UpperHalfPlane → ℂ) ∣[k]
        (mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) := fun F ↦ by
    rw [diamondOp_eq_diamondOpAux k d γ rfl]
    rfl
  have h_comm_app : diamondOp k d (heckeT_p k p hp hpN g.toModularForm') =
      heckeT_p k p hp hpN (diamondOp k d g.toModularForm') :=
    LinearMap.congr_fun
      (heckeT_p_comm_diamondOp (N := N) k p hp hpN d) g.toModularForm'
  have h_heckeT_p_congr : ∀ (F₁ F₂ : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      (⇑F₁ : UpperHalfPlane → ℂ) = ⇑F₂ →
      (⇑(heckeT_p k p hp hpN F₁) : UpperHalfPlane → ℂ) =
      ⇑(heckeT_p k p hp hpN F₂) := fun F₁ F₂ hF ↦ by
    show heckeT_p_fun k p hp hpN F₁ = heckeT_p_fun k p hp hpN F₂
    rw [heckeT_p_fun_eq_coset_sum k hp hpN F₁,
      heckeT_p_fun_eq_coset_sum k hp hpN F₂, hF]
  calc (⇑(diamondOp_cusp k d (heckeT_p_cusp k p hp hpN g)) :
        UpperHalfPlane → ℂ)
      = (⇑(heckeT_p_cusp k p hp hpN g) : UpperHalfPlane → ℂ) ∣[k]
          (mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) := h_diamond_cusp_coe _
    _ = (⇑(heckeT_p k p hp hpN g.toModularForm') : UpperHalfPlane → ℂ) ∣[k]
          (mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) := rfl
    _ = ⇑(diamondOp k d (heckeT_p k p hp hpN g.toModularForm')) :=
          (h_diamond_mf_coe _).symm
    _ = ⇑(heckeT_p k p hp hpN (diamondOp k d g.toModularForm')) := by
          rw [h_comm_app]
    _ = ⇑(heckeT_p k p hp hpN (diamondOp_cusp k d g).toModularForm') := by
          apply h_heckeT_p_congr
          rw [h_diamond_mf_coe, show (⇑(diamondOp_cusp k d g).toModularForm' :
            UpperHalfPlane → ℂ) = ⇑(diamondOp_cusp k d g) from rfl,
            h_diamond_cusp_coe]
          rfl
    _ = ⇑(heckeT_p_cusp k p hp hpN (diamondOp_cusp k d g)) := rfl

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T128 petN-level q-reindex consumer**: applying the T128 pointwise
identity across the full `∑_q : SL(2, ℤ) ⧸ Γ₁(N)` sum (via `Equiv.sum_comp`
on `σ = Gamma1QuotEquivOfGamma0 γ`, combined with T128 on the first
`peterssonInner` slot and T126 on the second) collapses to a `petN`
identity:
`petN (T_p f) g = petN (T_p (⟨Gamma0MapUnits γ⟩ f)) (⟨Gamma0MapUnits γ⟩ g)`
for any `γ ∈ Γ₀(N)` and Γ₁(N)-cusp forms `f, g`. -/
theorem petN_heckeT_p_Gamma1QuotEquiv_reindex
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (γ : ↥(Gamma0 N)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (heckeT_p_cusp k p hp hpN
              (diamondOp_cusp k (Gamma0MapUnits γ) f))
           (diamondOp_cusp k (Gamma0MapUnits γ) g) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
          (⇑(heckeT_p_cusp k p hp hpN f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
          (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
          (⇑(heckeT_p_cusp k p hp hpN
             (diamondOp_cusp k (Gamma0MapUnits γ) f)) ∣[k]
            (q.out : SL(2, ℤ))⁻¹)
          (⇑(diamondOp_cusp k (Gamma0MapUnits γ) g) ∣[k]
            (q.out : SL(2, ℤ))⁻¹)
  rw [← Equiv.sum_comp (Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property)
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹))]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [slash_heckeT_p_cusp_Gamma1QuotEquiv_out_inv_eq p hp hpN γ f q,
    slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv γ g q]

private theorem petN_heckeT_p_adjointGamma0Rep_reindex
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (heckeT_p_cusp k p hp hpN
              (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
           (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) := by
  have h := petN_heckeT_p_Gamma1QuotEquiv_reindex p hp hpN
    (adjointGamma0Rep p N hpN) f g
  rw [adjointGamma0Rep_units p N hpN] at h
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_f_heckeT_p_adjointGamma0Rep_reindex
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (heckeT_p_cusp k p hp hpN g) =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
        (heckeT_p_cusp k p hp hpN
          (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹)
          (⇑(heckeT_p_cusp k p hp hpN g) ∣[k] (q.out : SL(2, ℤ))⁻¹) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
            (q.out : SL(2, ℤ))⁻¹)
          (⇑(heckeT_p_cusp k p hp hpN
              (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            (q.out : SL(2, ℤ))⁻¹)
  rw [← Equiv.sum_comp (Gamma1QuotEquivOfGamma0
    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
    (adjointGamma0Rep p N hpN).property)
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ peterssonInner k ModularGroup.fd
        (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑(heckeT_p_cusp k p hp hpN g) ∣[k] (q.out : SL(2, ℤ))⁻¹))]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv
      (adjointGamma0Rep p N hpN) f q,
    slash_heckeT_p_cusp_Gamma1QuotEquiv_out_inv_eq p hp hpN
      (adjointGamma0Rep p N hpN) g q,
    adjointGamma0Rep_units p N hpN]

private lemma peterssonAdj_glMap_T_p_upper_zero_eq_glMap_T_p_lower
    (p : ℕ) (hp : 0 < p) :
    peterssonAdj (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) =
      (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  have h_L := peterssonAdj_glMap_T_p_upper p hp 0
  simp only [Nat.cast_zero, neg_zero] at h_L
  have h_R : ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, (1 : ℝ)] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;> simp [glMap, T_p_lower]
  show (peterssonAdj (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) :
      Matrix _ _ ℝ) i j =
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) : Matrix _ _ ℝ) i j
  rw [h_L, h_R]

private lemma slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_upper_zero_slash_gamma0
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      (⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
  have h_inv_prod :=
    glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp.pos hpN 0
  have h_M_infty_eq : (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN 0)) := by
    rw [← h_inv_prod, mul_inv_cancel_left]
  rw [h_M_infty_eq, peterssonAdj_mul, peterssonAdj_mapGL_SL_eq_inv,
    peterssonAdj_glMap_T_p_upper_zero_eq_glMap_T_p_lower]
  rw [← map_inv, SlashAction.slash_mul]
  have hfactor_mem := M_infty_Gamma1_factor_mem_Gamma1 N p hpN 0
  have hfactor_inv_mem : (M_infty_Gamma1_factor N p hpN 0)⁻¹ ∈ Gamma1 N :=
    inv_mem hfactor_mem
  have h_g_slash : ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (M_infty_Gamma1_factor N p hpN 0)⁻¹) = ⇑g :=
    SlashInvariantFormClass.slash_action_eq g _
      ⟨(M_infty_Gamma1_factor N p hpN 0)⁻¹, hfactor_inv_mem, rfl⟩
  rw [h_g_slash]
  exact slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0 p hp hpN g

private lemma slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_lower
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
  rw [slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_upper_zero_slash_gamma0
    p hp hpN g]
  exact (slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0 p hp hpN g).symm

private lemma slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower
    (p : ℕ) (hp : 0 < p) (b : ℕ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
      ⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) := by
  rw [peterssonAdj_T_p_upper_eq_shift_mul_lower p hp b, SlashAction.slash_mul,
    show (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (shiftSL_loc (-(b : ℤ))) : GL (Fin 2) ℝ)) = ⇑g from
        SlashInvariantFormClass.slash_action_eq g _
          ⟨shiftSL_loc (-(b : ℤ)), shiftSL_loc_mem_Gamma1 _, rfl⟩]

/-! ### T128 DS-standard `δ_b` representative-system helpers

The `δ_b ∈ Γ₁(N)` matrix realizing `γ₀ · T_p_upper(b) = T_p_lower · δ_b` for
`γ₀ = adjointGamma0Rep`.  These are the candidates for a complete
representative system of `H_L \ Γ₁(N)` where
`H_L := Γ₁(N) ∩ T_p_lower⁻¹ · Γ₁(N) · T_p_lower`. -/

private noncomputable def gamma0_T_p_upper_Gamma1_factor
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (b : ℕ) : SL(2, ℤ) :=
  ⟨!![1, (b : ℤ) - Int.gcdB p N;
      (N : ℤ), (N : ℤ) * b + (p : ℤ) * Int.gcdA p N],
    by
      have hbez := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
      rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
      rw [Matrix.det_fin_two_of]; linarith⟩

private theorem gamma0_T_p_upper_Gamma1_factor_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (b : ℕ) :
    gamma0_T_p_upper_Gamma1_factor N p hpN b ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have hbez := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
  rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
  have hN_zmod : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
  have hpgcdA_mod : ((p : ZMod N) : ZMod N) * ((Int.gcdA p N : ℤ) : ZMod N) = 1 := by
    have := congr_arg ((↑) : ℤ → ZMod N) hbez.symm
    push_cast at this
    rw [hN_zmod, zero_mul, add_zero] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · change ((1 : ℤ) : ZMod N) = 1
    push_cast; rfl
  · change (((N : ℤ) * b + (p : ℤ) * Int.gcdA p N : ℤ) : ZMod N) = 1
    push_cast
    rw [hN_zmod]
    simp only [zero_mul, zero_add]
    exact hpgcdA_mod
  · change (((N : ℤ) : ℤ) : ZMod N) = 0
    push_cast
    exact ZMod.natCast_self N

private theorem mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (b : ℕ) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  have hbez : (Int.gcdA p N : ℤ) * p + (Int.gcdB p N : ℤ) * N = 1 := by
    have h := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
    rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at h
    linarith
  have h_gamma0_mat : (((mapGL ℝ : SL(2, ℤ) →* _)
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), -((Int.gcdB p N : ℤ) : ℝ); (N : ℝ), ((Int.gcdA p N : ℤ) : ℝ)] := by
    ext i' j'
    fin_cases i' <;> fin_cases j' <;>
      simp [adjointGamma0Rep, mapGL_coe_matrix, algebraMap_int_eq, Matrix.of_apply]
  have h_Tu_mat : ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.map, Matrix.of_apply]
  have h_Tl_mat : ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [glMap, T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.map, Matrix.of_apply]
  have h_delta_mat : (((mapGL ℝ : SL(2, ℤ) →* _)
      (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), ((b : ℝ) - ((Int.gcdB p N : ℤ) : ℝ));
         (N : ℝ), ((N : ℝ) * b + (p : ℝ) * ((Int.gcdA p N : ℤ) : ℝ))] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [mapGL_coe_matrix, gamma0_T_p_upper_Gamma1_factor, algebraMap_int_eq,
        Matrix.of_apply]
  show ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : GL (Fin 2) ℝ).val i j =
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ)).val i j
  rw [Units.val_mul, Units.val_mul, h_gamma0_mat, h_Tu_mat, h_Tl_mat, h_delta_mat]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;> ring

private theorem mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
          M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) := by
  have h_M_infty_eq : (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN 0)) := by
    rw [← glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp hpN 0,
      mul_inv_cancel_left]
  rw [h_M_infty_eq, ← mul_assoc,
    mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp hpN 0,
    mul_assoc, ← map_mul]

private theorem gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    gamma0_T_p_upper_Gamma1_factor N p hpN 0 * M_infty_Gamma1_factor N p hpN 0 ∈
      Gamma1 N :=
  mul_mem (gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN 0)
    (M_infty_Gamma1_factor_mem_Gamma1 N p hpN 0)

private noncomputable def ds_p_plus_one_family_Gamma1_factor
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    Option (Fin p) → SL(2, ℤ)
  | none => gamma0_T_p_upper_Gamma1_factor N p hpN 0 * M_infty_Gamma1_factor N p hpN 0
  | some b => gamma0_T_p_upper_Gamma1_factor N p hpN b.val

private theorem ds_p_plus_one_family_Gamma1_factor_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (i : Option (Fin p)) :
    ds_p_plus_one_family_Gamma1_factor N p hpN i ∈ Gamma1 N := by
  match i with
  | none =>
    exact gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
      N p hpN
  | some b =>
    exact gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN b.val

private theorem mapGL_gamma0_mul_ds_family_eq_T_p_lower_mul_mapGL_factor
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      (match i with
        | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) := by
  match i with
  | none =>
    exact mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon N p hp hpN
  | some b =>
    exact mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp hpN b.val

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem gamma0_smul_ds_family_eq_T_p_lower_smul_gamma_X
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) (D : Set ℍ) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) •
      ((match i with
        | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      (((mapGL ℝ : SL(2, ℤ) →* _)
        (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) • D) := by
  rw [← mul_smul, ← mul_smul,
    mapGL_gamma0_mul_ds_family_eq_T_p_lower_mul_mapGL_factor N p hp hpN i]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem gamma0_smul_Hecke_FD_eq_T_p_lower_smul_iUnion
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (D : Set ℍ) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) •
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      (⋃ i : Option (Fin p),
        ((mapGL ℝ : SL(2, ℤ) →* _)
          (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) • D) := by
  rw [Set.smul_set_iUnion, Set.smul_set_iUnion]
  refine Set.iUnion_congr fun i ↦ ?_
  exact gamma0_smul_ds_family_eq_T_p_lower_smul_gamma_X (N := N) p hp hpN i D

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_gamma0_smul_Hecke_FD_eq_slash
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k
      (((mapGL ℝ : SL(2, ℤ) →* _)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      F G =
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ)) :=
  peterssonInner_mapGL_smul_eq_slash _
    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) F G

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_gamma0_smul_Hecke_FD_eq_T_p_lower_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k
      (((mapGL ℝ : SL(2, ℤ) →* _)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      F G =
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          ((mapGL ℝ : SL(2, ℤ) →* _)
            (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) • D))
      F G := by
  rw [gamma0_smul_Hecke_FD_eq_T_p_lower_smul_iUnion (N := N) p hp hpN D]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_lower_smul_eq_gamma0_slash
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          ((mapGL ℝ : SL(2, ℤ) →* _)
            (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) • D))
      F G =
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  rw [← peterssonInner_gamma0_smul_Hecke_FD_eq_T_p_lower_smul (N := N) p hp hpN D]
  exact peterssonInner_gamma0_smul_Hecke_FD_eq_slash (N := N) p hp hpN D F G

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_Hecke_FD_T_p_lower_slot2_slash_adjoint
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      F (G ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) =
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      (F ∣[k] (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ)) G := by
  have hα : 0 < (glMap (T_p_lower p hp) : GL (Fin 2) ℝ).det.val := by
    show 0 < ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_lower p hp : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_lower p hp : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_lower p hp : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_lower p hp : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp
  have h := peterssonInner_slash_adjoint_right (k := k)
    (⋃ i : Option (Fin p),
      (match i with
        | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) hα F G
  rw [peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero] at h
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_Hecke_FD_T_p_lower_slot1_slash_adjoint
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      (F ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) G =
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      F (G ∣[k] (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ)) := by
  have hα : 0 < (glMap (T_p_lower p hp) : GL (Fin 2) ℝ).det.val := by
    show 0 < ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_lower p hp : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_lower p hp : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_lower p hp : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_lower p hp : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp
  have h := peterssonInner_slash_adjoint (k := k)
    (⋃ i : Option (Fin p),
      (match i with
        | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) hα F G
  rw [peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero] at h
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_Hecke_FD_T_p_lower_residual_iff
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (f g : ℍ → ℂ) (g' : ℍ → ℂ) :
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      f (g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) =
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      (g' ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) g ↔
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      (f ∣[k] (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ)) g =
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      g' (g ∣[k] (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ)) := by
  rw [peterssonInner_Hecke_FD_T_p_lower_slot2_slash_adjoint
        (N := N) p hp hpN D f g,
      peterssonInner_Hecke_FD_T_p_lower_slot1_slash_adjoint
        (N := N) p hp hpN D g' g]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma UpperHalfPlane_smul_eq_of_matrix_smul_eq
    (α β : GL (Fin 2) ℝ) (hα : 0 < α.det.val) (hβ : 0 < β.det.val)
    (c : ℝ) (hc : c ≠ 0)
    (hMat : (α : Matrix (Fin 2) (Fin 2) ℝ) = c • (β : Matrix (Fin 2) (Fin 2) ℝ))
    (τ : ℍ) :
    α • τ = β • τ := by
  rw [UpperHalfPlane.ext_iff,
      UpperHalfPlane.coe_smul_of_det_pos hα,
      UpperHalfPlane.coe_smul_of_det_pos hβ]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom]
  have h00 : (α : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  have h01 : (α : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  have h10 : (α : Matrix (Fin 2) (Fin 2) ℝ) 1 0 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  have h11 : (α : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  rw [show ((α : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) by
    exact_mod_cast h00,
    show ((α : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) by
      exact_mod_cast h01,
    show ((α : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) by
      exact_mod_cast h10,
    show ((α : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) by
      exact_mod_cast h11]
  have hc_ne_zero : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have h_num : (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (τ : ℂ) +
      (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
      (c : ℂ) * (((β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (τ : ℂ) +
        ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ)) := by ring
  have h_den : (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (τ : ℂ) +
      (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
      (c : ℂ) * (((β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (τ : ℂ) +
        ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ)) := by ring
  rw [h_num, h_den, mul_div_mul_left _ _ hc_ne_zero]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_T_p_upper_smul_eq_shift_smul
    (p : ℕ) (hp : 0 < p) (b : ℕ) (τ : ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) • τ =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (shiftSL_loc (b : ℤ)) : GL (Fin 2) ℝ) • τ := by
  have hp_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h_det_pos_LHS : 0 <
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
        (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)).det.val := by
    show 0 < (((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show (((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
        (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) : Matrix _ _ ℝ) *
        ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : Matrix _ _ ℝ) from rfl,
      Matrix.det_mul]
    have h_T_p_lower : ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ) := by
      rw [show ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
          ((T_p_lower p hp : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
      rw [show (((T_p_lower p hp : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
          (algebraMap ℚ ℝ) (((T_p_lower p hp : GL (Fin 2) ℚ).val).det) from
            (RingHom.map_det _ _).symm]
      rw [show ((T_p_lower p hp : GL (Fin 2) ℚ).val).det = (p : ℚ) by
        simp [T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.det_fin_two, Matrix.of_apply]]
      show (algebraMap ℚ ℝ) ((p : ℚ)) = _
      rfl
    have h_T_p_upper : ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ) := by
      rw [show ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
          ((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
      rw [show (((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
          (algebraMap ℚ ℝ) (((T_p_upper p hp b : GL (Fin 2) ℚ).val).det) from
            (RingHom.map_det _ _).symm]
      rw [show ((T_p_upper p hp b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
        simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.det_fin_two, Matrix.of_apply]]
      show (algebraMap ℚ ℝ) ((p : ℚ)) = _
      rfl
    rw [h_T_p_lower, h_T_p_upper]
    positivity
  have h_det_pos_RHS : 0 <
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b : ℤ)) :
        GL (Fin 2) ℝ).det.val := by
    show 0 < (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b : ℤ)) :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b : ℤ)) :
        GL (Fin 2) ℝ).val = ((Int.castRingHom ℝ).mapMatrix
        (shiftSL_loc (b : ℤ)).val) by rw [mapGL_coe_matrix]; rfl]
    rw [← RingHom.map_det, (shiftSL_loc (b : ℤ)).property]
    norm_num
  refine UpperHalfPlane_smul_eq_of_matrix_smul_eq _ _ h_det_pos_LHS h_det_pos_RHS
    (p : ℝ) (by exact_mod_cast hp.ne') ?_ τ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glMap, T_p_lower, T_p_upper, mapGL_coe_matrix, shiftSL_loc,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.map,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Units.val_mul,
      algebraMap_int_eq, Matrix.smul_apply] <;>
    ring

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_M_infty_smul_eq_M_infty_Gamma1_factor_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (τ : ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)) • τ =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) • τ := by
  have h_M_infty_eq : (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (M_infty_Gamma1_factor N p hpN 0)) := by
    rw [← glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp hpN 0,
      mul_inv_cancel_left]
  rw [h_M_infty_eq, ← mul_assoc, mul_smul]
  rw [T_p_lower_mul_T_p_upper_smul_eq_shift_smul p hp 0]
  show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc ((0 : ℕ) : ℤ))
    : GL (Fin 2) ℝ) • _ = _
  rw [show shiftSL_loc ((0 : ℕ) : ℤ) = (1 : SL(2, ℤ)) by
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shiftSL_loc, Matrix.of_apply]]
  simp [MonoidHom.map_one, one_smul]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma smul_set_eq_of_smul_eq
    {α β : GL (Fin 2) ℝ} (hsmul : ∀ τ : ℍ, α • τ = β • τ) (S : Set ℍ) :
    α • S = β • S := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, (hsmul σ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, hsmul σ⟩

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_T_p_upper_smul_set_eq_shift_smul
    (p : ℕ) (hp : 0 < p) (b : ℕ) (S : Set ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) • S =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (shiftSL_loc (b : ℤ)) : GL (Fin 2) ℝ) • S :=
  smul_set_eq_of_smul_eq (T_p_lower_mul_T_p_upper_smul_eq_shift_smul p hp b) S

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_M_infty_smul_set_eq_M_infty_Gamma1_factor_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (S : Set ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)) • S =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) • S :=
  smul_set_eq_of_smul_eq
    (T_p_lower_mul_M_infty_smul_eq_M_infty_Gamma1_factor_smul (N := N) p hp hpN) S

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma mapGL_sigma_p_smul_T_p_lower_smul_set_eq_M_infty_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (S : Set ℍ) :
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ) •
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) • S) =
    (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) • S := by
  rw [smul_smul,
    ← glMap_M_infty_eq_mapGL_sigma_p_mul_glMap_T_p_lower (N := N) p hp hpN]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma mapGL_sigma_p_inv_smul_M_infty_smul_set_eq_T_p_lower_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (S : Set ℍ) :
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ) •
      ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) • S) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) • S := by
  rw [← mapGL_sigma_p_smul_T_p_lower_smul_set_eq_M_infty_smul (N := N) p hp hpN S,
    smul_smul, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem M_infty_iUnion_eq_mapGL_sigma_p_smul_T_p_lower_iUnion
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ))) =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ) •
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun q ↦ ?_
  rw [mapGL_sigma_p_smul_T_p_lower_smul_set_eq_M_infty_smul (N := N) p hp hpN]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_M_infty_iUnion_eq_sigma_p_slash
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (F G : ℍ → ℂ) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      F G =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ)) := by
  rw [M_infty_iUnion_eq_mapGL_sigma_p_smul_T_p_lower_iUnion (N := N) p hp hpN]
  exact peterssonInner_mapGL_smul_eq_slash _ _ F G

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_LHS_M_infty_residual_after_sigma_p
    (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (G : ℍ → ℂ) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) G =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      ⇑f
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ)) := by
  rw [peterssonInner_M_infty_iUnion_eq_sigma_p_slash (N := N) p hp hpN,
    slash_sigma_p_diamond_inv_cusp_eq p hp hpN f]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_RHS_M_infty_residual_after_sigma_p
    (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N)
    (F : ℍ → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      F ⇑g =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ))
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) := by
  rw [peterssonInner_M_infty_iUnion_eq_sigma_p_slash (N := N) p hp hpN,
    ← coe_diamondOp_cusp_eq_slash_sigma_p p hp hpN g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_iUnion_eq_mapGL_sigma_p_inv_smul_M_infty_iUnion
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ))) =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ) •
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun q ↦ ?_
  rw [mapGL_sigma_p_inv_smul_M_infty_smul_set_eq_T_p_lower_smul (N := N) p hp hpN]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_lower_iUnion_eq_sigma_p_inv_slash
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (F G : ℍ → ℂ) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      F G =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ)) := by
  rw [T_p_lower_iUnion_eq_mapGL_sigma_p_inv_smul_M_infty_iUnion (N := N) p hp hpN]
  exact peterssonInner_mapGL_smul_eq_slash _ _ F G

private noncomputable def T_p_lower_tile_family
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    Option (Fin p) → SL(2, ℤ)
  | none => M_infty_Gamma1_factor N p hpN 0
  | some b => shiftSL_loc (b.val : ℤ)

private noncomputable def Hecke_rep_family
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    Option (Fin p) → GL (Fin 2) ℝ
  | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
  | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_smul_Hecke_FD_eq_iUnion_tile
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (S : Set ℍ) :
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      (⋃ i : Option (Fin p), Hecke_rep_family N p hp hpN i • S) =
    ⋃ i : Option (Fin p),
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun i ↦ ?_
  match i with
  | none =>
    show (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) • S) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) • S
    rw [← mul_smul]
    exact T_p_lower_mul_M_infty_smul_set_eq_M_infty_Gamma1_factor_smul
      (N := N) p hp hpN S
  | some b =>
    show (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) • S) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (shiftSL_loc (b.val : ℤ)) : GL (Fin 2) ℝ) • S
    rw [← mul_smul]
    exact T_p_lower_mul_T_p_upper_smul_set_eq_shift_smul p hp b.val S

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_lower_tile_eq_slash
    (p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (S : Set ℍ) (F G : ℍ → ℂ)
    (i : Option (Fin p)) :
    peterssonInner k
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) F G =
    peterssonInner k S
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ)) :=
  peterssonInner_mapGL_smul_eq_slash _ (T_p_lower_tile_family N p hpN i) F G

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_lower_iUnion_tile_eq_sum
    (p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (S : Set ℍ) (F G : ℍ → ℂ)
    (hm : ∀ i : Option (Fin p), NullMeasurableSet
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) μ_hyp)
    (hd : Pairwise (fun i j : Option (Fin p) ↦ AEDisjoint μ_hyp
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S)
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN j) : GL (Fin 2) ℝ) • S)))
    (hfi : IntegrableOn (fun τ ↦ petersson k F G τ)
      (⋃ i : Option (Fin p),
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) μ_hyp) :
    peterssonInner k
      (⋃ i : Option (Fin p),
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) F G =
    ∑ i : Option (Fin p), peterssonInner k
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) F G :=
  peterssonInner_iUnion_finite_aedisjoint _ hm hd F G hfi

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_lower_Hecke_FD_eq_sum_tile_slash
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (S : Set ℍ) (F G : ℍ → ℂ)
    (hm : ∀ i : Option (Fin p), NullMeasurableSet
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) μ_hyp)
    (hd : Pairwise (fun i j : Option (Fin p) ↦ AEDisjoint μ_hyp
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S)
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN j) : GL (Fin 2) ℝ) • S)))
    (hfi : IntegrableOn (fun τ ↦ petersson k F G τ)
      (⋃ i : Option (Fin p),
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) μ_hyp) :
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p), Hecke_rep_family N p hp hpN i • S)) F G =
    ∑ i : Option (Fin p), peterssonInner k S
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ)) := by
  rw [T_p_lower_smul_Hecke_FD_eq_iUnion_tile (N := N) p hp hpN S,
      peterssonInner_T_p_lower_iUnion_tile_eq_sum (N := N) p hpN S F G hm hd hfi]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact peterssonInner_T_p_lower_tile_eq_slash (N := N) p hpN S F G i

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem mapGL_tile_mul_peterssonAdj_Hecke_rep_eq_glMap_T_p_lower
    (p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) :
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) *
      peterssonAdj (Hecke_rep_family N p hp.pos hpN i) =
    (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
  match i with
  | none =>
    show ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN 0)
      : GL (Fin 2) ℝ) *
      peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)
    rw [show (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (M_infty_Gamma1_factor N p hpN 0)) by
      rw [← glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp.pos hpN 0,
        mul_inv_cancel_left]]
    rw [peterssonAdj_mul, peterssonAdj_mapGL_SL_eq_inv,
      peterssonAdj_glMap_T_p_upper_zero_eq_glMap_T_p_lower]
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (M_infty_Gamma1_factor N p hpN 0)) *
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (M_infty_Gamma1_factor N p hpN 0))⁻¹ *
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (M_infty_Gamma1_factor N p hpN 0) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (M_infty_Gamma1_factor N p hpN 0))⁻¹) *
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) by group]
    rw [mul_inv_cancel, one_mul]
  | some b =>
    show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b.val : ℤ))
      : GL (Fin 2) ℝ) *
      peterssonAdj (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) =
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)
    rw [peterssonAdj_T_p_upper_eq_shift_mul_lower p hp.pos b.val]
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b.val : ℤ))) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b.val : ℤ))) *
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b.val : ℤ)) *
          (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b.val : ℤ)))) *
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) by group]
    rw [← map_mul]
    rw [show shiftSL_loc (b.val : ℤ) * shiftSL_loc (-(b.val : ℤ)) =
        (1 : SL(2, ℤ)) by
      apply Subtype.ext; ext i j
      fin_cases i <;> fin_cases j <;>
        simp [shiftSL_loc, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]]
    rw [map_one, one_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_swap_via_uniform_adj
    (p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (F G : ℍ → ℂ) (i : Option (Fin p)) :
    peterssonInner k (fd : Set ℍ)
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))
      (G ∣[k] (Hecke_rep_family N p hp.pos hpN i)) =
    peterssonInner k (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
      (F ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) G := by
  have hα : 0 < (Hecke_rep_family N p hp.pos hpN i).det.val := by
    match i with
    | none =>
      exact glMap_M_infty_det_pos N p hp.pos hpN
    | some b =>
      show 0 < ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det
      rw [show ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
          ((T_p_upper p hp.pos b.val : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
      rw [show (((T_p_upper p hp.pos b.val : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
          (algebraMap ℚ ℝ) (((T_p_upper p hp.pos b.val : GL (Fin 2) ℚ).val).det) from
            (RingHom.map_det _ _).symm]
      rw [show ((T_p_upper p hp.pos b.val : GL (Fin 2) ℚ).val).det = (p : ℚ) by
        simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.det_fin_two, Matrix.of_apply]]
      show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
      rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
      exact_mod_cast hp.pos
  rw [peterssonInner_slash_adjoint_right _ _ hα]
  rw [show (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ)) ∣[k]
        peterssonAdj (Hecke_rep_family N p hp.pos hpN i) =
        F ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) by
    rw [← SlashAction.slash_mul,
      mapGL_tile_mul_peterssonAdj_Hecke_rep_eq_glMap_T_p_lower (N := N) p hp hpN i]]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_swap_via_uniform_adj_slot1
    (p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (F G : ℍ → ℂ) (i : Option (Fin p)) :
    peterssonInner k (fd : Set ℍ)
      (G ∣[k] (Hecke_rep_family N p hp.pos hpN i))
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ)) =
    peterssonInner k (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ)) G
      (F ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  rw [← peterssonInner_conj_symm,
      peterssonInner_swap_via_uniform_adj (N := N) p hp hpN F G i,
      peterssonInner_conj_symm]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_per_X_sum_iff_Hecke_FD_residual
    (p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : ℍ → ℂ)
    (hm : ∀ i : Option (Fin p), NullMeasurableSet
      (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ)) μ_hyp)
    (hd : Pairwise (fun i j : Option (Fin p) ↦ AEDisjoint μ_hyp
      (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
      (Hecke_rep_family N p hp.pos hpN j • (fd : Set ℍ))))
    (hfi_LHS : IntegrableOn (fun τ ↦ petersson k f
        (g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ)) μ_hyp)
    (hfi_RHS : IntegrableOn (fun τ ↦ petersson k
        (f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) g τ)
      (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ)) μ_hyp) :
    (∑ i : Option (Fin p), peterssonInner k (fd : Set ℍ)
      (f ∣[k] (Hecke_rep_family N p hp.pos hpN i))
      (g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))) =
      peterssonInner k
        (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
        f (g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∧
    (∑ i : Option (Fin p), peterssonInner k (fd : Set ℍ)
      (f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))
      (g ∣[k] (Hecke_rep_family N p hp.pos hpN i))) =
      peterssonInner k
        (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
        (f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) g := by
  refine ⟨?_, ?_⟩
  ·
    have h_per_X : ∀ i : Option (Fin p), peterssonInner k (fd : Set ℍ)
        (f ∣[k] (Hecke_rep_family N p hp.pos hpN i))
        (g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ)) =
        peterssonInner k (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
          f (g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := fun i ↦ peterssonInner_swap_via_uniform_adj_slot1 (N := N) p hp hpN g f i
    rw [Finset.sum_congr rfl (fun i _ ↦ h_per_X i)]
    exact (peterssonInner_iUnion_finite_aedisjoint
      (fun i : Option (Fin p) ↦ Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
      hm hd f (g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) hfi_LHS).symm
  ·
    have h_per_X : ∀ i : Option (Fin p), peterssonInner k (fd : Set ℍ)
        (f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))
        (g ∣[k] (Hecke_rep_family N p hp.pos hpN i)) =
        peterssonInner k (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
          (f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) g := fun i ↦ peterssonInner_swap_via_uniform_adj (N := N) p hp hpN f g i
    rw [Finset.sum_congr rfl (fun i _ ↦ h_per_X i)]
    exact (peterssonInner_iUnion_finite_aedisjoint
      (fun i : Option (Fin p) ↦ Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
      hm hd (f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) g hfi_RHS).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_smul_eq_of_matrix_proportional
    {α β : GL (Fin 2) ℝ} (hα : 0 < α.det.val) (hβ : 0 < β.det.val)
    (c : ℝ) (hc : c ≠ 0)
    (hMat : (α : Matrix (Fin 2) (Fin 2) ℝ) = c • (β : Matrix (Fin 2) (Fin 2) ℝ))
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k (α • D) F G = peterssonInner k (β • D) F G := by
  congr 1
  exact smul_set_eq_of_smul_eq
    (UpperHalfPlane_smul_eq_of_matrix_smul_eq α β hα hβ c hc hMat) D

open UpperHalfPlane ModularGroup MeasureTheory in
private def Hecke_FD_integral_residual
    (p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  peterssonInner k
    (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
    ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
  peterssonInner k
    (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_smul_set_GL_pos
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k (α • D) F G =
      ∫ τ in D, petersson k F G ((⟨α, hα⟩ : GL(2, ℝ)⁺) • τ) ∂μ_hyp := by
  simp only [peterssonInner]
  set α' : GL(2, ℝ)⁺ := ⟨α, hα⟩
  rw [show (α • D : Set ℍ) = (fun τ ↦ α' • τ) '' D by
    rw [Set.image_smul]; rfl]
  exact (measurePreserving_smul α' μ_hyp).setIntegral_image_emb
    (measurableEmbedding_const_smul α') _ D

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_slash_adj_M_infty_q_summand_eq
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  rw [peterssonInner_slash_adjoint_coset (glMap (M_infty N p hp.pos hpN))
        (glMap_M_infty_det_pos N p hp.pos hpN) q ⇑f ⇑g]
  rw [slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_upper_zero_slash_gamma0
    p hp hpN g]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_ds_p_plus_one_family_union_collapse_per_q_split
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) =
    peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ⇑f
          ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  rw [peterssonInner_slash_adj_M_infty_q_summand_eq p hp hpN q f g]
  congr 1
  exact sum_peterssonInner_upper_family_per_b_rewrite p hp hpN q f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_M_infty_plus_upper_union_tile_per_q
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfi_upper : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) =
    peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) +
      peterssonInner k
        (⋃ b ∈ Finset.range p,
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
              (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  rw [peterssonInner_ds_p_plus_one_family_union_collapse_per_q_split p hp hpN q f g]; congr 1
  rw [show (∑ b ∈ Finset.range p,
        peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
          ⇑f
          ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))) =
      ∑ b ∈ Finset.range p,
        peterssonInner k (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
          ⇑f
          ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) from
    Finset.sum_congr rfl fun b _ ↦ by rw [mul_smul]]
  exact peterssonInner_T_p_upper_family_union_collapse_per_q hp hpN q f g hfi_upper

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_glQ_then_mapGL_SL_eq_combinedGL
    (F : UpperHalfPlane → ℂ) (α : GL (Fin 2) ℚ) (δ : SL(2, ℤ)) :
    ((F ∣[k] ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ)) =
    F ∣[k] ((glMap α : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ)) := by
  rw [← SlashAction.slash_mul]
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_glQ_mapGLSL_to_combinedGL
    (F : UpperHalfPlane → ℂ) (α : GL (Fin 2) ℚ) (δ : SL(2, ℤ)) :
    ((F ∣[k] (α : GL (Fin 2) ℚ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ)) =
    F ∣[k] ((glMap α : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ)) := by
  change ((F ∣[k] (glMap α : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ)) =
    F ∣[k] ((glMap α : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ))
  rw [← SlashAction.slash_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_LHS_per_q_distribute
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) := by
  have h_Tpf : (⇑(heckeT_p_cusp k p hp hpN f) : UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos ⇑f.toModularForm' +
        ⇑f.toModularForm' ∣[k] (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) :=
    heckeT_p_fun_eq_coset_sum k hp hpN f.toModularForm'
  rw [h_Tpf, SlashAction.add_slash]
  rw [show heckeT_p_ut k p hp.pos ⇑f.toModularForm' =
      ∑ b ∈ Finset.range p,
        ⇑f.toModularForm' ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ) from rfl]
  rw [SlashAction.sum_slash]
  simp_rw [slash_glQ_mapGLSL_to_combinedGL]
  rw [add_comm]
  set G : UpperHalfPlane → ℂ :=
    ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) with hG_def
  set F0 : UpperHalfPlane → ℂ :=
    ⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hF0_def
  set F : ℕ → UpperHalfPlane → ℂ := fun b ↦ ⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hF_def
  have h0 : IntegrableOn (fun τ ↦ petersson k G F0 τ) ModularGroup.fd μ_hyp := by
    have h := integrableOn_petersson_cuspform_mixed_slash_on_fd
      (N := N) (k := k) g f (M_infty N p hp.pos hpN) q⁻¹
    show IntegrableOn (fun τ ↦ petersson k
      (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
      (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))) τ) ModularGroup.fd μ_hyp
    rw [show ⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) =
      (⇑f ∣[k] ((M_infty N p hp.pos hpN).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) from
      (slash_glQ_then_mapGL_SL_eq_combinedGL (k := k)
        ⇑f (M_infty N p hp.pos hpN) q⁻¹).symm]
    exact h
  have hF : ∀ b ∈ Finset.range p,
      IntegrableOn (fun τ ↦ petersson k G (F b) τ) ModularGroup.fd μ_hyp := by
    intro b _
    have h := integrableOn_petersson_cuspform_mixed_slash_on_fd
      (N := N) (k := k) g f (T_p_upper p hp.pos b) q⁻¹
    show IntegrableOn (fun τ ↦ petersson k
      (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
      (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))) τ) ModularGroup.fd μ_hyp
    rw [show ⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) =
      (⇑f ∣[k] ((T_p_upper p hp.pos b).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) from
      (slash_glQ_then_mapGL_SL_eq_combinedGL (k := k)
        ⇑f (T_p_upper p hp.pos b) q⁻¹).symm]
    exact h
  exact peterssonInner_add_finset_sum_left (Finset.range p) F0 F G ModularGroup.fd h0 hF

open UpperHalfPlane ModularGroup MeasureTheory ConjAct Pointwise in
private lemma integrableOn_petersson_upper_union_uniform_gslot_per_q
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IntegrableOn
      (fun τ ↦ petersson k ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp := by
  set A : GL (Fin 2) ℝ :=
    (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) with hA_def
  have h_integrand_eq :
      (fun τ ↦ petersson k ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ) =
      (fun τ ↦ petersson k ⇑f (⇑g ∣[k] A) τ) := by
    funext τ; rw [hA_def, SlashAction.slash_mul]
  rw [h_integrand_eq]
  set σ : GL (Fin 2) ℚ :=
    T_p_upper p hp.pos 0 *
      ((mapGL ℚ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) with hσ_def
  have h_σ_map :
      (((σ : GL (Fin 2) ℚ).map (Rat.castHom ℝ)) : GL (Fin 2) ℝ) = A := by
    show glMap σ = A
    rw [hσ_def, map_mul, glMap_mapGL_Q_eq_mapGL_R, hA_def]
  haveI hArith :
      (toConjAct (A : GL (Fin 2) ℝ)⁻¹ •
        ((Gamma1 N).map (mapGL ℝ))).IsArithmetic := by
    have h := Subgroup.IsArithmetic.conj ((Gamma1 N).map (mapGL ℝ)) σ⁻¹
    have h_inv : (((σ⁻¹ : GL (Fin 2) ℚ).map (Rat.castHom ℝ)) : GL (Fin 2) ℝ) =
        (A : GL (Fin 2) ℝ)⁻¹ := by
      rw [map_inv, h_σ_map]
    rw [h_inv] at h
    exact h
  let g_tr : CuspForm
      (toConjAct (A : GL (Fin 2) ℝ)⁻¹ • ((Gamma1 N).map (mapGL ℝ))) k :=
    CuspForm.translate g A
  have h_gtr_coe : (⇑g_tr : UpperHalfPlane → ℂ) = ⇑g ∣[k] A := rfl
  obtain ⟨C_f, hC_f⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f f
  obtain ⟨C_gtr, hC_gtr⟩ :=
    CuspFormClass.petersson_bounded_left k _ g_tr g_tr
  have h_AM_GM : ∀ τ,
      ‖petersson k ⇑f (⇑g ∣[k] A) τ‖ ≤ (C_f + C_gtr) / 2 := by
    intro τ
    rw [← h_gtr_coe]
    show ‖petersson k ⇑f ⇑g_tr τ‖ ≤ (C_f + C_gtr) / 2
    have h_norm_ineq : ‖petersson k ⇑f ⇑g_tr τ‖ ≤
        (‖petersson k ⇑f ⇑f τ‖ + ‖petersson k ⇑g_tr ⇑g_tr τ‖) / 2 := by
      simp only [petersson, norm_mul, Complex.norm_conj]
      have h_im_nn : (0 : ℝ) ≤ ‖((τ.im : ℂ) ^ k)‖ := norm_nonneg _
      nlinarith [mul_nonneg (sq_nonneg (‖(⇑f) τ‖ - ‖(⇑g_tr) τ‖)) h_im_nn,
        sq_nonneg (‖(⇑f) τ‖ - ‖(⇑g_tr) τ‖), norm_nonneg (⇑f τ),
        norm_nonneg (⇑g_tr τ), h_im_nn]
    linarith [hC_f τ, hC_gtr τ]
  have h_fd_null : NullMeasurableSet (ModularGroup.fd : Set UpperHalfPlane) μ_hyp :=
    ((isClosed_le continuous_const
        (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)).inter
      (isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re)
        continuous_const)).measurableSet.nullMeasurableSet
  have h_mapGL_mat_det_eq_one :
      (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [show (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix (q⁻¹ : SL(2, ℤ)).val) by
      rw [mapGL_coe_matrix]; rfl]
    rw [← RingHom.map_det, (q⁻¹ : SL(2, ℤ)).property]
    simp
  have h_Tp_det_pos : ∀ b,
      0 < (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ).det.val := fun b ↦ by
    show 0 < ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp.pos
  have h_α_det_pos : ∀ b,
      0 < ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)).det.val := fun b ↦ by
    show 0 < (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)) :
          Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)) :
            Matrix (Fin 2) (Fin 2) ℝ) =
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        (((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) from Units.val_mul _ _,
      Matrix.det_mul, h_mapGL_mat_det_eq_one, mul_one]
    exact h_Tp_det_pos b
  have h_finite_measure :
      μ_hyp (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) < ⊤ := by
    refine lt_of_le_of_lt (measure_biUnion_finset_le _ _) ?_
    refine ENNReal.sum_lt_top.mpr fun b _ ↦ ?_
    rw [measure_glPos_smul_eq _ (h_α_det_pos b) h_fd_null]
    exact hyperbolicMeasure_fd_lt_top
  refine IntegrableOn.of_bound h_finite_measure ?_ ((C_f + C_gtr) / 2) ?_
  · rw [← h_gtr_coe]
    exact (petersson_continuous k (ModularFormClass.continuous f.toModularForm')
      (ModularFormClass.continuous g_tr)).aestronglyMeasurable.restrict
  · exact ae_of_all _ fun τ ↦ h_AM_GM τ

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_LHS_per_q_to_union_tiles
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
      (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
      (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) +
    peterssonInner k
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
      ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  rw [peterssonInner_heckeT_p_LHS_per_q_distribute p hp hpN q f g]
  exact peterssonInner_M_infty_plus_upper_union_tile_per_q p hp hpN q f g
    (integrableOn_petersson_upper_union_uniform_gslot_per_q p hp hpN q f g)

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_LHS_per_q_to_union_tiles_T_p_lower_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
      (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
      (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k
      (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
        (ModularGroup.fd : Set UpperHalfPlane))
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
    peterssonInner k
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  rw [peterssonInner_heckeT_p_LHS_per_q_to_union_tiles p hp hpN q f g,
    show (⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) =
      ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) from
        (slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0 p hp hpN g).symm,
    ← mul_smul]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_eq_per_q_T_p_lower_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
       peterssonInner k
        (⋃ b ∈ Finset.range p,
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k] ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) = _
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  change peterssonInner k ModularGroup.fd
      (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ))
      (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
        GL (Fin 2) ℝ)) = _
  exact peterssonInner_heckeT_p_LHS_per_q_to_union_tiles_T_p_lower_form
    p hp hpN (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_eq_per_alpha_HeckeFD_form
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
    (h_M_infty_int : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
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
    (h_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
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
    (h_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp) :
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
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  rw [petN_heckeT_p_eq_per_q_T_p_lower_form p hp hpN f g, Finset.sum_add_distrib]
  congr 1
  ·
    exact (peterssonInner_iUnion_finite_aedisjoint
      (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
      h_M_infty_meas h_M_infty_disj ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) h_M_infty_int).symm
  ·
    have h_per_q_expand : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k
          (⋃ b ∈ Finset.range p,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
        ∑ b ∈ Finset.range p,
          peterssonInner k
            (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
            ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := fun q ↦ peterssonInner_biUnion_finset_ae (Finset.range p)
        (fun b hb ↦ h_upper_per_q_meas q b hb)
        (h_upper_per_q_disj q) ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
        (h_upper_per_q_int q)
    rw [show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
            peterssonInner k
              (⋃ b ∈ Finset.range p,
                ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                  ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                    GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
              ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
          ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
            ∑ b ∈ Finset.range p,
              peterssonInner k
                (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                  ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                    GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
                ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) from
        Finset.sum_congr rfl fun q _ ↦ h_per_q_expand q,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    exact (peterssonInner_iUnion_finite_aedisjoint
      (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
      (h_upper_meas b hb) (h_upper_disj b hb) ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
      (h_upper_int b hb)).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_diamond_heckeT_p_eq_per_alpha_HeckeFD_form
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
    (h_M_infty_int : IntegrableOn
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
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
    (h_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
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
    (h_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp) :
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
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g := by
  rw [← petN_conj_symm]
  rw [petN_heckeT_p_eq_per_alpha_HeckeFD_form p hp hpN g
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
    h_M_infty_disj h_M_infty_meas h_M_infty_int
    h_upper_disj h_upper_meas h_upper_int
    h_upper_per_q_disj h_upper_per_q_meas h_upper_per_q_int]
  rw [map_add, map_sum]
  congr 1
  · exact peterssonInner_conj_symm k _ _ _
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    exact peterssonInner_conj_symm k _ _ _

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_RHS_per_q_distribute
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑(heckeT_p_cusp k p hp hpN
            (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) := by
  have h_Tp_ug : (⇑(heckeT_p_cusp k p hp hpN
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) :
      UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' +
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' ∣[k]
        (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) :=
    heckeT_p_fun_eq_coset_sum k hp hpN
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm'
  rw [h_Tp_ug, SlashAction.add_slash]
  rw [show heckeT_p_ut k p hp.pos
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' =
      ∑ b ∈ Finset.range p,
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ) from rfl]
  rw [SlashAction.sum_slash]
  simp_rw [slash_glQ_mapGLSL_to_combinedGL]
  rw [add_comm]
  set F : UpperHalfPlane → ℂ :=
    ⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) with hF_def
  set G0 : UpperHalfPlane → ℂ :=
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hG0_def
  set G : ℕ → UpperHalfPlane → ℂ := fun b ↦ ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hG_def
  have h0 : IntegrableOn (fun τ ↦ petersson k F G0 τ) ModularGroup.fd μ_hyp := by
    have h := integrableOn_petersson_cuspform_mixed_slash_on_fd
      (N := N) (k := k) f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)
      (M_infty N p hp.pos hpN) q⁻¹
    show IntegrableOn (fun τ ↦ petersson k
      (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))) τ) ModularGroup.fd μ_hyp
    rw [show (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))) =
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((M_infty N p hp.pos hpN).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) from
      (slash_glQ_then_mapGL_SL_eq_combinedGL (k := k)
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)
        (M_infty N p hp.pos hpN) q⁻¹).symm]
    exact h
  have hG_int : ∀ b ∈ Finset.range p,
      IntegrableOn (fun τ ↦ petersson k F (G b) τ) ModularGroup.fd μ_hyp := by
    intro b _
    have h := integrableOn_petersson_cuspform_mixed_slash_on_fd
      (N := N) (k := k) f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)
      (T_p_upper p hp.pos b) q⁻¹
    show IntegrableOn (fun τ ↦ petersson k
      (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))) τ) ModularGroup.fd μ_hyp
    rw [show (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))) =
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((T_p_upper p hp.pos b).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) from
      (slash_glQ_then_mapGL_SL_eq_combinedGL (k := k)
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)
        (T_p_upper p hp.pos b) q⁻¹).symm]
    exact h
  exact peterssonInner_add_finset_sum_right (Finset.range p) F G0 G ModularGroup.fd h0 hG_int

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_symm_RHS_per_q_distribute
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑(heckeT_p_cusp k p hp hpN g) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) := by
  rw [coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f]
  have h_Tp_g : (⇑(heckeT_p_cusp k p hp hpN g) : UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos ⇑g.toModularForm' +
      ⇑g.toModularForm' ∣[k]
        (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) :=
    heckeT_p_fun_eq_coset_sum k hp hpN g.toModularForm'
  rw [h_Tp_g, SlashAction.add_slash]
  rw [show heckeT_p_ut k p hp.pos ⇑g.toModularForm' =
      ∑ b ∈ Finset.range p,
        ⇑g.toModularForm' ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ) from rfl]
  rw [SlashAction.sum_slash]
  simp_rw [slash_glQ_mapGLSL_to_combinedGL]
  rw [add_comm]
  set F : UpperHalfPlane → ℂ :=
    (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
      GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) with hF_def
  set G0 : UpperHalfPlane → ℂ :=
    ⇑g ∣[k]
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hG0_def
  set G : ℕ → UpperHalfPlane → ℂ := fun b ↦ ⇑g ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hG_def
  have h0 : IntegrableOn (fun τ ↦ petersson k F G0 τ) ModularGroup.fd μ_hyp := by
    have h := integrableOn_petersson_cuspform_mixed_slash_on_fd
      (N := N) (k := k) (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) g
      (M_infty N p hp.pos hpN) q⁻¹
    show IntegrableOn (fun τ ↦ petersson k
      ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
      (⇑g ∣[k]
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))) τ) ModularGroup.fd μ_hyp
    rw [show (⇑g ∣[k]
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))) =
      (⇑g ∣[k]
        ((M_infty N p hp.pos hpN).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) from
      (slash_glQ_then_mapGL_SL_eq_combinedGL (k := k) ⇑g
        (M_infty N p hp.pos hpN) q⁻¹).symm]
    rw [← coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f]
    exact h
  have hG_int : ∀ b ∈ Finset.range p,
      IntegrableOn (fun τ ↦ petersson k F (G b) τ) ModularGroup.fd μ_hyp := by
    intro b _
    have h := integrableOn_petersson_cuspform_mixed_slash_on_fd
      (N := N) (k := k) (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) g
      (T_p_upper p hp.pos b) q⁻¹
    show IntegrableOn (fun τ ↦ petersson k
      ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
      (⇑g ∣[k]
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))) τ) ModularGroup.fd μ_hyp
    rw [show (⇑g ∣[k]
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))) =
      (⇑g ∣[k]
        ((T_p_upper p hp.pos b).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) from
      (slash_glQ_then_mapGL_SL_eq_combinedGL (k := k) ⇑g
        (T_p_upper p hp.pos b) q⁻¹).symm]
    rw [← coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f]
    exact h
  exact peterssonInner_add_finset_sum_right (Finset.range p) F G0 G ModularGroup.fd h0 hG_int

open UpperHalfPlane ModularGroup in
private lemma slash_diamond_inv_T_p_upper_eq_T_p_lower_delta
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ) (q : SL(2, ℤ))
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    ⇑g ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  have h_diamond : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
      UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    show ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = _
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  rw [h_diamond, ← SlashAction.slash_mul, ← mul_assoc,
    mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp.pos hpN b]

open UpperHalfPlane ModularGroup in
private lemma slash_diamond_inv_M_infty_eq_T_p_lower_epsilon
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (q : SL(2, ℤ))
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    ⇑g ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  have h_diamond : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
      UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    show ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = _
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  rw [h_diamond, ← SlashAction.slash_mul, ← mul_assoc,
    mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon N p hp.pos hpN]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_RHS_per_q_normalized
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑(heckeT_p_cusp k p hp hpN
            (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
                GL (Fin 2) ℝ))) := by
  rw [peterssonInner_heckeT_p_RHS_per_q_distribute p hp hpN q f g]
  congr 1
  · rw [slash_diamond_inv_M_infty_eq_T_p_lower_epsilon p hp hpN q g]
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [slash_diamond_inv_T_p_upper_eq_T_p_lower_delta p hp hpN b q g]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_SL_inv_eq_mapGL_inv
    (F G : UpperHalfPlane → ℂ) (q : SL(2, ℤ)) :
    peterssonInner k ModularGroup.fd
      (F ∣[k] (q⁻¹ : SL(2, ℤ)))
      (G ∣[k] (q⁻¹ : SL(2, ℤ))) =
    peterssonInner k ModularGroup.fd
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_diamond_heckeT_p_symm_RHS_sum_distributed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (⇑(heckeT_p_cusp k p hp hpN g) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) = _
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [peterssonInner_SL_inv_eq_mapGL_inv]
  exact peterssonInner_heckeT_p_symm_RHS_per_q_distribute p hp hpN
    (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_f_heckeT_p_RHS_sum_normalized
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (heckeT_p_cusp k p hp hpN
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                  M_infty_Gamma1_factor N p hpN 0)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((q.out : SL(2, ℤ))⁻¹))
        (⇑(heckeT_p_cusp k p hp hpN
            (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) = _
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [peterssonInner_SL_inv_eq_mapGL_inv]
  exact peterssonInner_heckeT_p_RHS_per_q_normalized p hp hpN
    (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_T_p_lower_slash_adj_coset_right_Gamma1_twist
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q * γ⁻¹)⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        ⇑g := by
  have hq'_inv : ((q * γ⁻¹)⁻¹ : SL(2, ℤ)) = γ * q⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  have h_slash_γ : (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ :
      GL (Fin 2) ℝ)) = ⇑f := by
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) =
          ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) from rfl, ← ModularForm.SL_slash]
    exact slash_Gamma1_eq f γ hγ
  have h_g_slash_chain :
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) ((q * γ⁻¹)⁻¹ : SL(2, ℤ)) :
          GL (Fin 2) ℝ) := by
    rw [hq'_inv, map_mul, ← mul_assoc]
  have h_f_slash_eq :
      (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
      (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) ((q * γ⁻¹)⁻¹ : SL(2, ℤ)) :
        GL (Fin 2) ℝ)) := by
    rw [hq'_inv, map_mul, SlashAction.slash_mul, h_slash_γ]
  rw [h_g_slash_chain, h_f_slash_eq]
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
  rw [peterssonInner_slash_adjoint_coset_right
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) h_det_pos (q * γ⁻¹) ⇑f ⇑g]
  rw [peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero p hp.pos]

private lemma glMap_M_infty_mul_mapGL_inv_eq_gamma0_inv_mul_shifted
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (q : SL(2, ℤ)) :
    (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
          GL (Fin 2) ℝ)⁻¹ *
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ :
            GL (Fin 2) ℝ)) := by
  have h_core :=
    mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon N p hp.pos hpN
  have h_inv_rewrite :
      ((q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
        M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ : SL(2, ℤ)) =
      (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
        M_infty_Gamma1_factor N p hpN 0) * q⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  rw [h_inv_rewrite, map_mul,
    ← mul_assoc (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ), ← h_core]
  group

private lemma peterssonInner_LHS_M_infty_tile_g_slot_to_peterssonAdj
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    UpperHalfPlane.peterssonInner k
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
    UpperHalfPlane.peterssonInner k
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      (⇑g ∣[k]
        peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) := by
  rw [← slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_upper_zero_slash_gamma0
      p hp hpN g]

private lemma glMap_T_p_upper_mul_mapGL_inv_eq_gamma0_inv_mul_shifted
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ) (q : SL(2, ℤ)) :
    (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
          GL (Fin 2) ℝ)⁻¹ *
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
            GL (Fin 2) ℝ)) := by
  have h_core :=
    mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp.pos hpN b
  have h_inv_rewrite :
      ((q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ : SL(2, ℤ)) =
      gamma0_T_p_upper_Gamma1_factor N p hpN b * q⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  rw [h_inv_rewrite, map_mul,
    ← mul_assoc (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ), ← h_core]
  group

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_RHS_per_q_normalized_shifted_tile
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
              GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
                GL (Fin 2) ℝ))) =
    peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        ⇑g +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          ⇑g := by
  rw [peterssonInner_T_p_lower_slash_adj_coset_right_Gamma1_twist p hp hpN q
        (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
          M_infty_Gamma1_factor N p hpN 0)
        (gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
          N p hpN) f g]
  congr 1
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  exact peterssonInner_T_p_lower_slash_adj_coset_right_Gamma1_twist p hp hpN q
    (gamma0_T_p_upper_Gamma1_factor N p hpN b)
    (gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN b) f g

open UpperHalfPlane ModularGroup MeasureTheory in
open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_symm_RHS_per_q_M_infty_branch_shifted_tile_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ)) := by
  have h := peterssonInner_T_p_lower_slash_adj_coset_right_Gamma1_twist p hp hpN q
    (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
      M_infty_Gamma1_factor N p hpN 0)
    (gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
      N p hpN)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g)
  rw [coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f,
      coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN g] at h
  conv_lhs =>
    rw [glMap_M_infty_mul_mapGL_inv_eq_gamma0_inv_mul_shifted p hp hpN q,
      SlashAction.slash_mul,
      show (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ))⁻¹ =
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) from (map_inv _ _).symm,
      show ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ : GL (Fin 2) ℝ)) =
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) by
        rw [mul_inv_rev, inv_inv, map_mul, ← mul_assoc]]
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_symm_RHS_per_q_upper_branch_shifted_tile_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
              GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ)) := by
  have h := peterssonInner_T_p_lower_slash_adj_coset_right_Gamma1_twist p hp hpN q
    (gamma0_T_p_upper_Gamma1_factor N p hpN b)
    (gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN b)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g)
  rw [coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f,
      coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN g] at h
  conv_lhs =>
    rw [glMap_T_p_upper_mul_mapGL_inv_eq_gamma0_inv_mul_shifted p hp hpN b q,
      SlashAction.slash_mul,
      show (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ))⁻¹ =
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) from (map_inv _ _).symm,
      show ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
            GL (Fin 2) ℝ)) =
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b) :
            GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) by
        rw [mul_inv_rev, inv_inv, map_mul, ← mul_assoc]]
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_symm_RHS_per_q_distribute_shifted_tile_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) := by
  rw [peterssonInner_heckeT_p_symm_RHS_per_q_M_infty_branch_shifted_tile_residual
      p hp hpN q f g]
  congr 1
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  exact peterssonInner_heckeT_p_symm_RHS_per_q_upper_branch_shifted_tile_residual
    p hp hpN b q f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_diamond_heckeT_p_symm_RHS_sum_shifted_tile_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ)) *
                  (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                    M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) +
        ∑ b ∈ Finset.range p,
          peterssonInner k
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((q.out : SL(2, ℤ)) *
                    (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                  GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
            (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ))) := by
  rw [petN_diamond_heckeT_p_symm_RHS_sum_distributed p hp hpN f g]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  exact peterssonInner_heckeT_p_symm_RHS_per_q_distribute_shifted_tile_residual
    p hp hpN (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_f_heckeT_p_RHS_sum_shifted_tiles
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (heckeT_p_cusp k p hp hpN
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ)) *
                  (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                    M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          ⇑g +
        ∑ b ∈ Finset.range p,
          peterssonInner k
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((q.out : SL(2, ℤ)) *
                    (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                  GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
            (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
            ⇑g) := by
  rw [petN_f_heckeT_p_RHS_sum_normalized p hp hpN f g]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  exact peterssonInner_heckeT_p_RHS_per_q_normalized_shifted_tile p hp hpN
    (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_symm_residual_sum_eq_standard_shifted_tiles
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ)) *
                  (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                    M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) +
        ∑ b ∈ Finset.range p,
          peterssonInner k
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((q.out : SL(2, ℤ)) *
                    (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                  GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
            (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ)) *
                  (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                    M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          ⇑g +
        ∑ b ∈ Finset.range p,
          peterssonInner k
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((q.out : SL(2, ℤ)) *
                    (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                  GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
            (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
            ⇑g) := by
  rw [← petN_diamond_heckeT_p_symm_RHS_sum_shifted_tile_residual p hp hpN f g,
      ← petN_f_heckeT_p_RHS_sum_shifted_tiles p hp hpN f g]
  have h := petN_f_heckeT_p_adjointGamma0Rep_reindex p hp hpN
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) g
  rw [show (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = f by
    show diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (diamondOpCusp k (ZMod.unitOfCoprime p hpN) f) = f
    rw [show diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (diamondOpCusp k (ZMod.unitOfCoprime p hpN) f) =
        ((diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹).comp
          (diamondOpCusp k (ZMod.unitOfCoprime p hpN))) f from rfl,
      ← diamondOpCusp_mul, inv_mul_cancel, diamondOpCusp_one]
    rfl] at h
  exact h

private lemma petN_diamond_heckeT_p_eq_canonical_RHS
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) =
      petN f (heckeT_p_cusp k p hp hpN
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) := by
  rw [petN_diamond_heckeT_p_symm_RHS_sum_shifted_tile_residual p hp hpN f g,
      petN_symm_residual_sum_eq_standard_shifted_tiles p hp hpN f g,
      ← petN_f_heckeT_p_RHS_sum_shifted_tiles p hp hpN f g]

private lemma heckeT_p_cusp_comm_diamondOp_private
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (d : (ZMod N)ˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_p_cusp k p hp hpN (diamondOp_cusp k d g) =
      diamondOp_cusp k d (heckeT_p_cusp k p hp hpN g) := by
  apply CuspForm.ext; intro τ
  show ((heckeT_p k p hp hpN) (diamondOp k d g.toModularForm')).toFun τ =
    ((diamondOp k d) (heckeT_p k p hp hpN g.toModularForm')).toFun τ
  have h := LinearMap.congr_fun
    (heckeT_p_comm_diamondOp (N := N) k p hp hpN d) g.toModularForm'
  simp only [LinearMap.comp_apply] at h
  exact congr_arg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k ↦ m.toFun τ)
    h.symm

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_T_p_heckeT_p_LHS_sum_distributed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹)) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) = _
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [peterssonInner_SL_inv_eq_mapGL_inv]
  exact peterssonInner_heckeT_p_LHS_per_q_distribute p hp hpN
    (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_T_p_heckeT_p_LHS_sum_diamond_distributed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
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
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) := by
  rw [petN_heckeT_p_adjointGamma0Rep_reindex p hp hpN f g]
  rw [petN_T_p_heckeT_p_LHS_sum_distributed p hp hpN
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have h_diamond_g : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
      UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    show ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = _
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  congr 1
  ·
    rw [slash_diamond_inv_M_infty_eq_T_p_lower_epsilon p hp hpN
      (q.out : SL(2, ℤ)) f]
    rw [show (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) =
      ⇑g ∣[k]
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) by
      rw [h_diamond_g, ← SlashAction.slash_mul]]
  ·
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [slash_diamond_inv_T_p_upper_eq_T_p_lower_delta p hp hpN b
      (q.out : SL(2, ℤ)) f]
    rw [show (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) =
      ⇑g ∣[k]
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) by
      rw [h_diamond_g, ← SlashAction.slash_mul]]

private lemma petN_diamond_heckeT_p_eq_unsymm_RHS
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  rw [petN_diamond_heckeT_p_eq_canonical_RHS p hp hpN f g,
      heckeT_p_cusp_comm_diamondOp_private p hp hpN
        (ZMod.unitOfCoprime p hpN)⁻¹ g]

/-! ### T024 DS double-coset tile bridge interface -/

open UpperHalfPlane ModularGroup MeasureTheory in
private def DSDoubleCosetTileBridge
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
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_of_doubleCosetTileBridge
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_bridge : DSDoubleCosetTileBridge p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  unfold DSDoubleCosetTileBridge at h_bridge
  rw [petN_T_p_heckeT_p_LHS_sum_diamond_distributed p hp hpN f g, h_bridge,
    ← petN_diamond_heckeT_p_symm_RHS_sum_distributed p hp hpN f g,
    petN_diamond_heckeT_p_eq_unsymm_RHS p hp hpN f g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_symmetric_form_of_doubleCosetTileBridge
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_bridge : DSDoubleCosetTileBridge p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) := by
  rw [petN_heckeT_p_adjoint_standard_form_of_doubleCosetTileBridge
        p hp hpN f g h_bridge,
      ← petN_diamond_heckeT_p_eq_unsymm_RHS p hp hpN f g]

private abbrev petN_doubleCoset_adjoint_adjugate
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  DSDoubleCosetTileBridge (k := k) p hp hpN f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) := by
  set σ : SL(2, ℤ) ⧸ Gamma1 N ≃ SL(2, ℤ) ⧸ Gamma1 N :=
    Gamma1QuotEquivOfGamma0
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
      (adjointGamma0Rep p N hpN).property
  exact (σ.sum_comp _).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv_GL
    (γ : ↥(Gamma0 N)) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      ((Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property q).out :
        SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) =
    ⇑(diamondOp_cusp k (Gamma0MapUnits γ) g) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) :=
  slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv γ g q

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_diamond_outAt_Gamma1QuotEquiv_eq_slash_outAt
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((Gamma1QuotEquivOfGamma0
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
          (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹) =
    ⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (q.out : SL(2, ℤ))⁻¹) := by
  rw [show (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ)) =
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) :
        UpperHalfPlane → ℂ) from
    (coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f).symm]
  rw [slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv_GL
    (adjointGamma0Rep p N hpN)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) q]
  rw [adjointGamma0Rep_units p N hpN]
  congr 1
  show ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (diamondOpCusp k (ZMod.unitOfCoprime p hpN) f)) = ⇑f
  rw [show diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (diamondOpCusp k (ZMod.unitOfCoprime p hpN) f) =
      ((diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹).comp
        (diamondOpCusp k (ZMod.unitOfCoprime p hpN))) f from rfl,
    ← diamondOpCusp_mul, inv_mul_cancel, diamondOpCusp_one]
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_M_infty_eq_diamond_slash_T_p_lower_factor
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ)) :
    ⇑g ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  have h := slash_diamond_inv_M_infty_eq_T_p_lower_epsilon p hp hpN q
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g)
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
private lemma slash_T_p_upper_eq_diamond_slash_T_p_lower_factor
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ)) :
    ⇑g ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  have h := slash_diamond_inv_T_p_upper_eq_T_p_lower_delta p hp hpN b q
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g)
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
private lemma peterssonInner_diamond_inv_T_p_upper_eq_T_p_lower
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (D : Set ℍ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (G : ℍ → ℂ) :
    peterssonInner k D
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) G =
      peterssonInner k D
        (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)))) G := by
  have h := slash_diamond_inv_T_p_upper_eq_T_p_lower_delta p hp hpN b 1 f
  simp only [inv_one, map_one, mul_one] at h
  rw [h]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_slash_T_p_upper_eq_diamond_T_p_lower_cusp_g
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (D : Set ℍ) (F : ℍ → ℂ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k D F
        (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) =
      peterssonInner k D F
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)))) := by
  have h := slash_T_p_upper_eq_diamond_slash_T_p_lower_factor p hp hpN b g 1
  simp only [inv_one, map_one, mul_one] at h
  rw [h]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma per_q_M_infty_branch_full_absorb
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    peterssonInner k ModularGroup.fd
      ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out :
            SL(2, ℤ))⁻¹))
      (⇑g ∣[k]
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((Gamma1QuotEquivOfGamma0
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
              (adjointGamma0Rep p N hpN).property q).out :
              SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
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
  rw [slash_diamond_outAt_Gamma1QuotEquiv_eq_slash_outAt p hp hpN f q]
  rw [slash_M_infty_eq_diamond_slash_T_p_lower_factor p hp hpN g
    (Gamma1QuotEquivOfGamma0
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
      (adjointGamma0Rep p N hpN).property q).out]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma per_q_T_p_upper_branch_full_absorb
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    peterssonInner k ModularGroup.fd
      ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out :
            SL(2, ℤ))⁻¹))
      (⇑g ∣[k]
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((Gamma1QuotEquivOfGamma0
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
              (adjointGamma0Rep p N hpN).property q).out :
              SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
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
  rw [slash_diamond_outAt_Gamma1QuotEquiv_eq_slash_outAt p hp hpN f q]
  rw [slash_T_p_upper_eq_diamond_slash_T_p_lower_factor p hp hpN b g
    (Gamma1QuotEquivOfGamma0
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
      (adjointGamma0Rep p N hpN).property q).out]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_T_p_lower_factor_eq_diamond_inv_slash_M_infty
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ)) :
    ⇑f ∣[k] ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  have h := slash_M_infty_eq_diamond_slash_T_p_lower_factor p hp hpN
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) q
  rw [show (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = f by
    show diamondOpCusp k (ZMod.unitOfCoprime p hpN)
      (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) = f
    rw [show diamondOpCusp k (ZMod.unitOfCoprime p hpN)
        (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) =
        ((diamondOpCusp k (ZMod.unitOfCoprime p hpN)).comp
          (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹)) f from rfl,
      ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
    rfl] at h
  exact h.symm

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_LHS_M_infty_per_q_to_tile_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set UpperHalfPlane)))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  rw [slash_T_p_lower_factor_eq_diamond_inv_slash_M_infty p hp hpN f q]
  have h_diamond_inv_g : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
        UpperHalfPlane → ℂ) = ⇑g ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    have h := coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)
    rw [show (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = g by
      show diamondOpCusp k (ZMod.unitOfCoprime p hpN)
        (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = g
      rw [show diamondOpCusp k (ZMod.unitOfCoprime p hpN)
          (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) =
          ((diamondOpCusp k (ZMod.unitOfCoprime p hpN)).comp
            (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹)) g from rfl,
        ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
      rfl] at h
    have h2 := congr_arg (fun F : UpperHalfPlane → ℂ ↦ F ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) h
    simp only at h2
    rw [← SlashAction.slash_mul, ← map_mul, inv_mul_cancel, map_one,
      SlashAction.slash_one] at h2
    exact h2.symm
  rw [show (⇑g ∣[k]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) by
    rw [SlashAction.slash_mul, ← h_diamond_inv_g]]
  exact peterssonInner_slash_adj_M_infty_q_summand_eq p hp hpN q
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_T_p_lower_b_factor_eq_diamond_inv_slash_T_p_upper
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ)) :
    ⇑f ∣[k] ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  have h := slash_T_p_upper_eq_diamond_slash_T_p_lower_factor p hp hpN b
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) q
  rw [show (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = f by
    show diamondOpCusp k (ZMod.unitOfCoprime p hpN)
      (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) = f
    rw [show diamondOpCusp k (ZMod.unitOfCoprime p hpN)
        (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) =
        ((diamondOpCusp k (ZMod.unitOfCoprime p hpN)).comp
          (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹)) f from rfl,
      ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
    rfl] at h
  exact h.symm

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_LHS_upper_per_q_to_tile_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set UpperHalfPlane)))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  rw [slash_T_p_lower_b_factor_eq_diamond_inv_slash_T_p_upper p hp hpN b f q]
  have h_diamond_inv_g : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
        UpperHalfPlane → ℂ) = ⇑g ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    have h := coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)
    rw [show (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = g by
      show diamondOpCusp k (ZMod.unitOfCoprime p hpN)
        (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = g
      rw [show diamondOpCusp k (ZMod.unitOfCoprime p hpN)
          (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) =
          ((diamondOpCusp k (ZMod.unitOfCoprime p hpN)).comp
            (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹)) g from rfl,
        ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
      rfl] at h
    have h2 := congr_arg (fun F : UpperHalfPlane → ℂ ↦ F ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) h
    simp only at h2
    rw [← SlashAction.slash_mul, ← map_mul, inv_mul_cancel, map_one,
      SlashAction.slash_one] at h2
    exact h2.symm
  rw [show (⇑g ∣[k]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) by
    rw [SlashAction.slash_mul, ← h_diamond_inv_g]]
  exact peterssonInner_slash_adj_T_p_upper_q_summand_eq p hp hpN b q
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma sum_peterssonInner_LHS_M_infty_to_tile_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
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
      peterssonInner k ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  refine Finset.sum_congr rfl (fun q _ ↦ ?_)
  exact peterssonInner_LHS_M_infty_per_q_to_tile_form p hp hpN
    ((q.out : SL(2, ℤ)) : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma sum_peterssonInner_LHS_upper_to_tile_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
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
        peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  refine Finset.sum_congr rfl (fun q _ ↦ Finset.sum_congr rfl (fun b _ ↦ ?_))
  exact peterssonInner_LHS_upper_per_q_to_tile_form p hp hpN b
    ((q.out : SL(2, ℤ)) : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma sum_peterssonInner_M_infty_tile_form_collapse
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
    (h_int : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
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
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) :=
  (peterssonInner_iUnion_finite_aedisjoint
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ)))
    h_meas h_disj
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
    h_int).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_RHS_M_infty_per_q_to_tile_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set UpperHalfPlane)))
      ((⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
      (⇑g) := by
  rw [← slash_M_infty_eq_diamond_slash_T_p_lower_factor p hp hpN g q]
  have hβ : 0 < ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)).det.val := by
    show 0 < ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) :
      GL (Fin 2) ℝ).val.det
    rw [Units.val_mul, Matrix.det_mul]
    have h2 : ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
        Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
          Matrix (Fin 2) (Fin 2) ℝ) =
          ((Int.castRingHom ℝ).mapMatrix (q⁻¹).val) by
        rw [mapGL_coe_matrix]; rfl]
      rw [← RingHom.map_det, (q⁻¹).property]; simp
    rw [h2, mul_one]
    exact glMap_M_infty_det_pos N p hp.pos hpN
  have hslash := peterssonInner_slash_adjoint_right (k := k)
    (D := (fd : Set ℍ))
    (α := (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
    hβ
    ((⇑f : ℍ → ℂ) ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
    (⇑g)
  rw [hslash]
  rw [show ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
        (fd : Set ℍ) =
      (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) • fd from
    mul_smul _ _ _]
  rw [peterssonAdj_mul, peterssonAdj_mapGL_SL_eq_inv,
    show (mapGL ℝ q⁻¹)⁻¹ = (mapGL ℝ q : GL (Fin 2) ℝ) by
      rw [← map_inv, inv_inv]]
  rw [show ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
        GL (Fin 2) ℝ)) ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q *
        peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))) =
      ⇑f ∣[k] peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) by
    rw [← SlashAction.slash_mul, ← mul_assoc,
      show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q) = 1 by
        rw [← map_mul, inv_mul_cancel, map_one], one_mul]]
  rw [slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_upper_zero_slash_gamma0 p hp hpN f]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_RHS_upper_per_q_to_tile_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set UpperHalfPlane)))
      ((⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
      (⇑g) := by
  rw [← slash_T_p_upper_eq_diamond_slash_T_p_lower_factor p hp hpN b g q]
  have hβ : 0 < ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)).det.val := by
    show 0 < ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) :
      GL (Fin 2) ℝ).val.det
    rw [Units.val_mul, Matrix.det_mul]
    have h2 : ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
        Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
          Matrix (Fin 2) (Fin 2) ℝ) =
          ((Int.castRingHom ℝ).mapMatrix (q⁻¹).val) by
        rw [mapGL_coe_matrix]; rfl]
      rw [← RingHom.map_det, (q⁻¹).property]; simp
    rw [h2, mul_one]
    show 0 < ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_upper p hp.pos b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp.pos
  have hslash := peterssonInner_slash_adjoint_right (k := k)
    (D := (fd : Set ℍ))
    (α := (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
    hβ
    ((⇑f : ℍ → ℂ) ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
    (⇑g)
  rw [hslash]
  rw [show ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
        (fd : Set ℍ) =
      (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) • fd from
    mul_smul _ _ _]
  rw [peterssonAdj_mul, peterssonAdj_mapGL_SL_eq_inv,
    show (mapGL ℝ q⁻¹)⁻¹ = (mapGL ℝ q : GL (Fin 2) ℝ) by
      rw [← map_inv, inv_inv]]
  rw [show ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
        GL (Fin 2) ℝ)) ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q *
        peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) =
      ⇑f ∣[k] peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) by
    rw [← SlashAction.slash_mul, ← mul_assoc,
      show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q) = 1 by
        rw [← map_mul, inv_mul_cancel, map_one], one_mul]]
  rw [slash_peterssonAdj_T_p_upper_eq_slash_T_p_upper_zero_slash_gamma0 p hp hpN b f]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_RHS_M_infty_sigma_reindex_per_q_to_tile_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set UpperHalfPlane)))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
      (⇑g) := by
  have h := peterssonInner_slash_adj_M_infty_q_summand_eq p hp hpN q g
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
  have h1 := peterssonInner_conj_symm k ModularGroup.fd
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) : ℍ → ℂ) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
    ((⇑g : ℍ → ℂ) ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
  have h2 := peterssonInner_conj_symm k
    ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
      ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set ℍ)))
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
    (⇑g)
  rw [← h1, h, h2]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_RHS_upper_sigma_reindex_per_q_to_tile_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set UpperHalfPlane)))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
      (⇑g) := by
  have h := peterssonInner_slash_adj_T_p_upper_q_summand_eq p hp hpN b q g
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
  have h1 := peterssonInner_conj_symm k ModularGroup.fd
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) : ℍ → ℂ) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
    ((⇑g : ℍ → ℂ) ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
  have h2 := peterssonInner_conj_symm k
    ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
      ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set ℍ)))
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
    (⇑g)
  rw [← h1, h, h2]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma sum_peterssonInner_RHS_M_infty_to_tile_form_via_sigma
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
        (⇑g) := by
  rw [show (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
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
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((Gamma1QuotEquivOfGamma0
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
              (adjointGamma0Rep p N hpN).property q).out :
              SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) from
    Finset.sum_congr rfl (fun q _ ↦ (per_q_M_infty_branch_full_absorb p hp hpN f g q).symm)]
  rw [Equiv.sum_comp (Gamma1QuotEquivOfGamma0
    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
    (adjointGamma0Rep p N hpN).property)
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))]
  refine Finset.sum_congr rfl (fun q _ ↦ ?_)
  rw [show ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) =
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) by
    congr 1
    exact (coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f).symm]
  exact peterssonInner_RHS_M_infty_sigma_reindex_per_q_to_tile_form
    p hp hpN (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma sum_peterssonInner_RHS_upper_to_tile_form_via_sigma_per_b
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
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
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
        (⇑g) := by
  rw [show (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
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
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((Gamma1QuotEquivOfGamma0
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
              (adjointGamma0Rep p N hpN).property q).out :
              SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) from
    Finset.sum_congr rfl (fun q _ ↦ (per_q_T_p_upper_branch_full_absorb p hp hpN b f g q).symm)]
  rw [Equiv.sum_comp (Gamma1QuotEquivOfGamma0
    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
    (adjointGamma0Rep p N hpN).property)
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))]
  refine Finset.sum_congr rfl (fun q _ ↦ ?_)
  rw [show ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) =
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) by
    congr 1
    exact (coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f).symm]
  exact peterssonInner_RHS_upper_sigma_reindex_per_q_to_tile_form
    p hp hpN b (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma sum_peterssonInner_upper_tile_form_swap
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
    ∑ b ∈ Finset.range p,
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) :=
  Finset.sum_comm

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma sum_peterssonInner_upper_tile_form_per_b_collapse
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ) (hb : b ∈ Finset.range p)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_disj : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q₁.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q₂.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))))
    (h_int : IntegrableOn
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
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
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
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) :=
  (peterssonInner_iUnion_finite_aedisjoint
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ)))
    h_meas h_disj
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
    h_int).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex_absorbed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) =
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
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [per_q_M_infty_branch_full_absorb p hp hpN f g q]
  congr 1
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  exact per_q_T_p_upper_branch_full_absorb p hp hpN b f g q

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_heckeT_p_LHS_per_q_via_tile_bundle
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {ι : Type*} [Fintype ι] {T : Set UpperHalfPlane}
    (F : FiniteTileFundamentalDomain μ_hyp ι T)
    (g_const : UpperHalfPlane → ℂ)
    (h_LHS_eq_target : peterssonInner k ModularGroup.fd
      (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
      (⇑g ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
      peterssonInner k T ⇑f g_const)
    (h_int : IntegrableOn (fun τ ↦ petersson k ⇑f g_const τ) F.union μ_hyp) :
    peterssonInner k ModularGroup.fd
      (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
      (⇑g ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
      ∑ i : ι, peterssonInner k (F.tile i) ⇑f g_const := by
  rw [h_LHS_eq_target, F.peterssonInner_eq_sum _ _ h_int]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_T_p_heckeT_p_LHS_via_tile_bundle
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {ι : SL(2, ℤ) ⧸ Gamma1 N → Type*} [hFt : ∀ q, Fintype (ι q)]
    {T : SL(2, ℤ) ⧸ Gamma1 N → Set UpperHalfPlane}
    (F : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      FiniteTileFundamentalDomain μ_hyp (ι q) (T q))
    (g_const : UpperHalfPlane → ℂ)
    (h_LHS_eq_target : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) =
        peterssonInner k (T q) ⇑f g_const)
    (h_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑f g_const τ) (F q).union μ_hyp) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ i : ι q, peterssonInner k ((F q).tile i) ⇑f g_const := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) = _
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [peterssonInner_SL_inv_eq_mapGL_inv]
  exact peterssonInner_heckeT_p_LHS_per_q_via_tile_bundle p hp hpN
    (q.out : SL(2, ℤ)) f g (F q) g_const (h_LHS_eq_target q) (h_int q)

private theorem petN_heckeT_p_adjoint_standard_form_of_LHS_bridge
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_LHS : petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g)) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  rw [h_LHS, petN_diamond_heckeT_p_eq_unsymm_RHS p hp hpN f g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_of_tile_bundle
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {ι : SL(2, ℤ) ⧸ Gamma1 N → Type*} [hFt : ∀ q, Fintype (ι q)]
    {T : SL(2, ℤ) ⧸ Gamma1 N → Set UpperHalfPlane}
    (F : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      FiniteTileFundamentalDomain μ_hyp (ι q) (T q))
    (g_const : UpperHalfPlane → ℂ)
    (h_LHS_eq_target : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) =
        peterssonInner k (T q) ⇑f g_const)
    (h_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑f g_const τ) (F q).union μ_hyp)
    (h_tile_match : ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ i : ι q, peterssonInner k ((F q).tile i) ⇑f g_const =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g)) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  refine petN_heckeT_p_adjoint_standard_form_of_LHS_bridge p hp hpN f g ?_
  rw [petN_T_p_heckeT_p_LHS_via_tile_bundle p hp hpN f g F g_const
    h_LHS_eq_target h_int, h_tile_match]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_of_per_q_tile_match
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {ι : SL(2, ℤ) ⧸ Gamma1 N → Type*} [hFt : ∀ q, Fintype (ι q)]
    {T : SL(2, ℤ) ⧸ Gamma1 N → Set UpperHalfPlane}
    (F : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      FiniteTileFundamentalDomain μ_hyp (ι q) (T q))
    (g_const : UpperHalfPlane → ℂ)
    (h_LHS_eq_target : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) =
        peterssonInner k (T q) ⇑f g_const)
    (h_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑f g_const τ) (F q).union μ_hyp)
    (h_per_q_tile_match : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ i : ι q, peterssonInner k ((F q).tile i) ⇑f g_const =
      (peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  refine petN_heckeT_p_adjoint_standard_form_of_tile_bundle p hp hpN f g F
    g_const h_LHS_eq_target h_int ?_
  rw [petN_diamond_heckeT_p_symm_RHS_sum_distributed p hp hpN f g]
  exact Finset.sum_congr rfl fun q _ ↦ h_per_q_tile_match q

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_M_infty_T_p_upper_tile_sum_matches_per_q_distribute
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g_const : UpperHalfPlane → ℂ)
    (tile : Fin (p + 1) → Set UpperHalfPlane)
    (h_tile_zero_match :
      peterssonInner k (tile 0) ⇑f g_const =
      peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))
    (h_tile_succ_match : ∀ b : Fin p,
      peterssonInner k (tile b.succ) ⇑f g_const =
      peterssonInner k ModularGroup.fd
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :
    ∑ i : Fin (p + 1), peterssonInner k (tile i) ⇑f g_const =
      peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  rw [Fin.sum_univ_succ, h_tile_zero_match]
  congr 1
  rw [show (∑ b : Fin p, peterssonInner k (tile b.succ) ⇑f g_const) =
      ∑ b : Fin p,
        peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
    from Finset.sum_congr rfl fun b _ ↦ h_tile_succ_match b]
  exact Fin.sum_univ_eq_sum_range
    (fun n : ℕ ↦ peterssonInner k ModularGroup.fd
      ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹))
      (⇑g ∣[k]
        ((glMap (T_p_upper p hp.pos n) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) p

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_per_tile_match_via_slash_adjoint
    (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val)
    {tile_target : Set UpperHalfPlane}
    (F G : UpperHalfPlane → ℂ)
    (slot1_target slot2_target : UpperHalfPlane → ℂ)
    (h_tile_eq : tile_target =ᵐ[μ_hyp] β • ModularGroup.fd)
    (h_slash_slot1 : F ∣[k] β = slot1_target)
    (h_slash_slot2 : G ∣[k] (peterssonAdj β)⁻¹ = slot2_target) :
    peterssonInner k tile_target F G =
      peterssonInner k ModularGroup.fd slot1_target slot2_target := by
  have h_tile_inner :
      peterssonInner k tile_target F G =
        peterssonInner k (β • ModularGroup.fd) F G := by
    simp only [peterssonInner]
    exact setIntegral_congr_set h_tile_eq
  rw [h_tile_inner]
  have h_G_decomp : G = (G ∣[k] (peterssonAdj β)⁻¹) ∣[k] peterssonAdj β := by
    rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  conv_lhs => rw [h_G_decomp]
  rw [← peterssonInner_slash_adjoint ModularGroup.fd β hβ F
        (G ∣[k] (peterssonAdj β)⁻¹), h_slash_slot1, h_slash_slot2]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_per_tile_match_M_infty_branch
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (F g_const : UpperHalfPlane → ℂ)
    {tile_zero : Set UpperHalfPlane}
    (h_β_pos : 0 < (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹)).det.val)
    (h_tile_eq : tile_zero =ᵐ[μ_hyp]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) • ModularGroup.fd)
    (h_slash_slot2 :
      g_const ∣[k] (peterssonAdj
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹)))⁻¹ =
      ⇑g ∣[k]
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) :
    peterssonInner k tile_zero F g_const =
      peterssonInner k ModularGroup.fd
        ((F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  refine peterssonInner_per_tile_match_via_slash_adjoint _ h_β_pos F g_const _ _
    h_tile_eq ?_ h_slash_slot2
  exact SlashAction.slash_mul _ _ _ F

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_per_tile_match_T_p_upper_branch
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (F g_const : UpperHalfPlane → ℂ)
    {tile_b : Set UpperHalfPlane}
    (h_β_pos : 0 < (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹)).det.val)
    (h_tile_eq : tile_b =ᵐ[μ_hyp]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) • ModularGroup.fd)
    (h_slash_slot2 :
      g_const ∣[k] (peterssonAdj
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹)))⁻¹ =
      ⇑g ∣[k]
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) :
    peterssonInner k tile_b F g_const =
      peterssonInner k ModularGroup.fd
        ((F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  refine peterssonInner_per_tile_match_via_slash_adjoint _ h_β_pos F g_const _ _
    h_tile_eq ?_ h_slash_slot2
  exact SlashAction.slash_mul _ _ _ F

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_per_tile_match_M_infty_branch_closed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (F : UpperHalfPlane → ℂ)
    {tile_zero : Set UpperHalfPlane}
    (h_tile_eq : tile_zero =ᵐ[μ_hyp]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) • ModularGroup.fd) :
    peterssonInner k tile_zero F
      (⇑g ∣[k]
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
            GL (Fin 2) ℝ))) =
      peterssonInner k ModularGroup.fd
        ((F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  have h_β_pos : 0 < (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹)).det.val := by
    rw [← map_mul]
    set α := ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹ * (q.out : SL(2, ℤ))⁻¹
    show 0 < ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) α : GL (Fin 2) ℝ).val.det
    rw [show (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) α : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix α.val) by rw [mapGL_coe_matrix]; rfl,
      ← RingHom.map_det, α.property]
    norm_num
  have h_slash_slot2 :
      (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
              GL (Fin 2) ℝ))) ∣[k]
        (peterssonAdj
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹)))⁻¹ =
      ⇑g ∣[k]
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
    rw [← map_mul (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ),
      peterssonAdj_inv_mapGL_SL_eq_self, ← SlashAction.slash_mul, map_mul]
    congr 1
    rw [mul_assoc, ← mul_assoc ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ),
      ← map_mul, mul_inv_cancel, map_one, one_mul]
  exact peterssonInner_per_tile_match_M_infty_branch p hp hpN q g F
    (⇑g ∣[k]
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
          GL (Fin 2) ℝ)))
    h_β_pos h_tile_eq h_slash_slot2

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_per_tile_match_T_p_upper_branch_closed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (F : UpperHalfPlane → ℂ)
    {tile_b : Set UpperHalfPlane}
    (h_tile_eq : tile_b =ᵐ[μ_hyp]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) • ModularGroup.fd) :
    peterssonInner k tile_b F
      (⇑g ∣[k]
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
            GL (Fin 2) ℝ))) =
      peterssonInner k ModularGroup.fd
        ((F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  have h_β_pos : 0 < (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
        GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹)).det.val := by
    rw [← map_mul]
    set α := ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹ * (q.out : SL(2, ℤ))⁻¹
    show 0 < ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) α : GL (Fin 2) ℝ).val.det
    rw [show (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) α : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix α.val) by rw [mapGL_coe_matrix]; rfl,
      ← RingHom.map_det, α.property]
    norm_num
  have h_slash_slot2 :
      (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
              GL (Fin 2) ℝ))) ∣[k]
        (peterssonAdj
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹)))⁻¹ =
      ⇑g ∣[k]
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
    rw [← map_mul (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ),
      peterssonAdj_inv_mapGL_SL_eq_self, ← SlashAction.slash_mul, map_mul]
    congr 1
    rw [mul_assoc, ← mul_assoc ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ),
      ← map_mul, mul_inv_cancel, map_one, one_mul]
  exact peterssonInner_per_tile_match_T_p_upper_branch p hp hpN b q g F
    (⇑g ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
          GL (Fin 2) ℝ)))
    h_β_pos h_tile_eq h_slash_slot2

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_per_q_distributed_form_via_closed_branches
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (F : UpperHalfPlane → ℂ)
    (tile : Fin (p + 1) → Set UpperHalfPlane)
    (h_tile_eq : ∀ i : Fin (p + 1), tile i =ᵐ[μ_hyp]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) • ModularGroup.fd) :
    peterssonInner k (tile 0) F
      (⇑g ∣[k]
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
            GL (Fin 2) ℝ))) +
      ∑ b : Fin p, peterssonInner k (tile b.succ) F
        (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
              GL (Fin 2) ℝ))) =
      peterssonInner k ModularGroup.fd
          ((F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            ((F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  congr 1
  · exact peterssonInner_per_tile_match_M_infty_branch_closed p hp hpN q g F
      (h_tile_eq 0)
  ·
    rw [show (∑ b : Fin p, peterssonInner k (tile b.succ) F
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                  GL (Fin 2) ℝ)))) =
        ∑ b : Fin p, peterssonInner k ModularGroup.fd
          ((F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
      from Finset.sum_congr rfl fun b _ ↦ peterssonInner_per_tile_match_T_p_upper_branch_closed p hp hpN b.val q g F
          (h_tile_eq b.succ)]
    exact Fin.sum_univ_eq_sum_range
      (fun n : ℕ ↦ peterssonInner k ModularGroup.fd
        ((F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos n) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) p

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_via_closed_branches
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (tile : SL(2, ℤ) ⧸ Gamma1 N → Fin (p + 1) → Set UpperHalfPlane)
    (h_tile_eq : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ i : Fin (p + 1),
      tile q i =ᵐ[μ_hyp]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) • ModularGroup.fd)
    (h_LHS_eq_closed_branch_sum :
      petN (heckeT_p_cusp k p hp hpN f) g =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        (peterssonInner k (tile q 0) ⇑f
            (⇑g ∣[k]
              ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                  GL (Fin 2) ℝ))) +
          ∑ b : Fin p, peterssonInner k (tile q b.succ) ⇑f
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                  GL (Fin 2) ℝ))))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  refine petN_heckeT_p_adjoint_standard_form_of_LHS_bridge p hp hpN f g ?_
  rw [h_LHS_eq_closed_branch_sum,
    petN_diamond_heckeT_p_symm_RHS_sum_distributed p hp hpN f g]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  exact peterssonInner_per_q_distributed_form_via_closed_branches p hp hpN q g ⇑f
    (tile q) (h_tile_eq q)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_LHS_eq_closed_branch_sum_via_per_q
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (tile : SL(2, ℤ) ⧸ Gamma1 N → Fin (p + 1) → Set UpperHalfPlane)
    (h_per_q_LHS_eq_closed_branch_sum : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) =
      peterssonInner k (tile q 0) ⇑f
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                GL (Fin 2) ℝ))) +
        ∑ b : Fin p, peterssonInner k (tile q b.succ) ⇑f
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                GL (Fin 2) ℝ)))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        (peterssonInner k (tile q 0) ⇑f
            (⇑g ∣[k]
              ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                  GL (Fin 2) ℝ))) +
          ∑ b : Fin p, peterssonInner k (tile q b.succ) ⇑f
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                  GL (Fin 2) ℝ)))) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) = _
  exact Finset.sum_congr rfl fun q _ ↦ h_per_q_LHS_eq_closed_branch_sum q

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_per_q_LHS_eq_closed_branch_sum
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (tile : Fin (p + 1) → Set UpperHalfPlane)
    (h_M_infty_branch_per_q :
      peterssonInner k
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ⇑f
          ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
        peterssonInner k (tile 0) ⇑f
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                GL (Fin 2) ℝ))))
    (h_T_p_upper_branches_union_per_q :
      peterssonInner k
          (⋃ b ∈ Finset.range p,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
              (ModularGroup.fd : Set UpperHalfPlane))
          ⇑f
          ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
        ∑ b : Fin p, peterssonInner k (tile b.succ) ⇑f
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                GL (Fin 2) ℝ)))) :
    peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) =
      peterssonInner k (tile 0) ⇑f
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                GL (Fin 2) ℝ))) +
        ∑ b : Fin p, peterssonInner k (tile b.succ) ⇑f
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                GL (Fin 2) ℝ))) := by
  rw [peterssonInner_SL_inv_eq_mapGL_inv,
    peterssonInner_heckeT_p_LHS_per_q_to_union_tiles p hp hpN
      (q.out : SL(2, ℤ)) f g,
    h_M_infty_branch_per_q, h_T_p_upper_branches_union_per_q]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_aggregate_via_closed_branches
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (tile : SL(2, ℤ) ⧸ Gamma1 N → Fin (p + 1) → Set UpperHalfPlane)
    (h_tile_eq : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ i : Fin (p + 1),
      tile q i =ᵐ[μ_hyp]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) • ModularGroup.fd)
    (h_M_infty_branch_per_q : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ⇑f
          ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
        peterssonInner k (tile q 0) ⇑f
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                GL (Fin 2) ℝ))))
    (h_T_p_upper_branches_union_per_q : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (⋃ b ∈ Finset.range p,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
              (ModularGroup.fd : Set UpperHalfPlane))
          ⇑f
          ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
        ∑ b : Fin p, peterssonInner k (tile q b.succ) ⇑f
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
                GL (Fin 2) ℝ)))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  refine petN_heckeT_p_adjoint_standard_form_via_closed_branches p hp hpN f g
    tile h_tile_eq ?_
  refine petN_LHS_eq_closed_branch_sum_via_per_q p hp hpN f g tile ?_
  intro q
  exact peterssonInner_per_q_LHS_eq_closed_branch_sum p hp hpN q f g (tile q)
    (h_M_infty_branch_per_q q) (h_T_p_upper_branches_union_per_q q)

-- **NOTE (T024 review).**  The closed-branch consumer chain above
-- (`petN_heckeT_p_adjoint_standard_form_aggregate_via_closed_branches`,
-- `petN_LHS_eq_closed_branch_sum_via_per_q`,
-- `peterssonInner_per_q_LHS_eq_closed_branch_sum`,
-- `petN_heckeT_p_adjoint_standard_form_via_closed_branches`,
-- `peterssonInner_per_q_distributed_form_via_closed_branches`,
-- `peterssonInner_per_tile_match_*_branch{,_closed}`) is **conditional/exploratory**:
-- its per-q `h_M_infty_branch_per_q` and `h_T_p_upper_branches_union_per_q`
-- hypotheses are **mathematically false per-q** (the slot-1 determinants of the
-- M_∞ tile-shifted form (`det = p`) and the per-q distributed RHS form
-- (`det = 1`) cannot be matched per `q`).  The genuine
-- `petN(T_p f, g) = petN(⟨u⟩ f, T_p g)` identity matches only at the
-- sum-over-q level via the Q-reindex (`Gamma1QuotEquivOfGamma0`).  The
-- final route is the sum-level absorbed-RHS chain below
-- (`petN_heckeT_p_LHS_eq_diamond_T_p_g_via_sum_chain`).

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem M_infty_branch_RHS_unfactor_slot2
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
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
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) =
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
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  exact (slash_M_infty_eq_diamond_slash_T_p_lower_factor p hp hpN g
    (Gamma1QuotEquivOfGamma0
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
      (adjointGamma0Rep p N hpN).property q).out).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem M_infty_branch_LHS_sigma_reindex
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
          (⇑f ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                  M_infty_Gamma1_factor N p hpN 0)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k]
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  set σ : SL(2, ℤ) ⧸ Gamma1 N ≃ SL(2, ℤ) ⧸ Gamma1 N :=
    Gamma1QuotEquivOfGamma0
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
      (adjointGamma0Rep p N hpN).property
  exact (σ.sum_comp _).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem M_infty_branch_LHS_normalize_to_diamond
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have h_diamond : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
      UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    show ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = _
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  rw [show (⇑f ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
    from (slash_diamond_inv_M_infty_eq_T_p_lower_epsilon p hp hpN
      (q.out : SL(2, ℤ)) f).symm]
  rw [show (⇑g ∣[k]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
    by rw [SlashAction.slash_mul, ← h_diamond]]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem M_infty_branch_sum_slash_adjoint_reindex_prefactored
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
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
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  rw [M_infty_branch_LHS_normalize_to_diamond p hp hpN f g]
  rw [show (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
    from Finset.sum_congr rfl fun q _ ↦ peterssonInner_slash_adj_M_infty_q_summand_eq p hp hpN
        (q.out : SL(2, ℤ))
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)]
  exact h_tile_shift_to_prefactored

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem M_infty_branch_hypothesis_via_sum_chain
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
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
  rw [M_infty_branch_sum_slash_adjoint_reindex_prefactored p hp hpN f g
    h_tile_shift_to_prefactored,
    ← M_infty_branch_RHS_unfactor_slot2 p hp hpN f g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_upper_branch_RHS_unfactor_slot2
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  congr 1
  exact (slash_T_p_upper_eq_diamond_slash_T_p_lower_factor p hp hpN b g
    (Gamma1QuotEquivOfGamma0
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
      (adjointGamma0Rep p N hpN).property q).out).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_upper_branch_LHS_normalize_to_diamond
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have h_diamond : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
      UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    show ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = _
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  rw [show (⇑f ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
    from (slash_diamond_inv_T_p_upper_eq_T_p_lower_delta p hp hpN b
      (q.out : SL(2, ℤ)) f).symm]
  rw [show (⇑g ∣[k]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
    by rw [SlashAction.slash_mul, ← h_diamond]]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_upper_branch_sum_slash_adjoint_reindex_prefactored
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
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  rw [T_p_upper_branch_LHS_normalize_to_diamond p hp hpN f g]
  rw [show (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
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
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
    from Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun b _ ↦ peterssonInner_slash_adj_T_p_upper_q_summand_eq p hp hpN b
        (q.out : SL(2, ℤ))
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)]
  exact h_upper_tile_shift_to_prefactored

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_upper_branch_hypothesis_via_sum_chain
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
  rw [T_p_upper_branch_sum_slash_adjoint_reindex_prefactored p hp hpN f g
    h_upper_tile_shift_to_prefactored,
    ← T_p_upper_branch_RHS_unfactor_slot2 p hp hpN f g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_LHS_dist_eq_RHS_absorbed_from_branches
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M_infty_branch :
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
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))
    (h_upper_branch :
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
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h_M_infty_branch,
    h_upper_branch]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem M_infty_slot_swap_LHS_via_slash_adjoint_coset
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (F G : UpperHalfPlane → ℂ) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          (F ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        F
        (G ∣[k] peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  exact peterssonInner_slash_adjoint_coset
    (glMap (M_infty N p hp.pos hpN))
    (glMap_M_infty_det_pos N p hp.pos hpN) (q.out : SL(2, ℤ)) F G

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem M_infty_slot_swap_peterssonAdj_simplify
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (F G : UpperHalfPlane → ℂ) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        F
        (G ∣[k] peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        F
        (G ∣[k] ((glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) (sigma_p_specific N p hp.pos hpN)⁻¹))) := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  rw [peterssonAdj_glMap_M_infty_eq N p hp.pos hpN]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_sum_M_infty_residual_LHS_to_dist
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  exact (peterssonInner_slash_adj_M_infty_q_summand_eq p hp hpN
    (q.out : SL(2, ℤ))
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_sum_M_infty_LHS_dist_slot2_to_sigma
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  have h := slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv_GL
    (adjointGamma0Rep p N hpN) g q
  rw [adjointGamma0Rep_units p N hpN] at h
  exact h.symm

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_sum_M_infty_LHS_dist_slot1_unfactor_diamond
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
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
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  exact slash_diamond_inv_M_infty_eq_T_p_lower_epsilon p hp hpN
    (q.out : SL(2, ℤ)) f

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_M_infty_tile_shift_to_prefactored_of_FD_slash_exchange
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_FD_slash_exchange :
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
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :
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
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  rw [peterssonInner_sum_M_infty_residual_LHS_to_dist p hp hpN f g,
      peterssonInner_sum_M_infty_LHS_dist_slot2_to_sigma p hp hpN f g,
      peterssonInner_sum_M_infty_LHS_dist_slot1_unfactor_diamond p hp hpN f g]
  exact h_FD_slash_exchange

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_sum_T_p_upper_residual_LHS_to_dist
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  exact (peterssonInner_slash_adj_T_p_upper_q_summand_eq p hp hpN b
    (q.out : SL(2, ℤ))
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_sum_T_p_upper_LHS_dist_slot2_to_sigma
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑g ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  congr 1
  have h := slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv_GL
    (adjointGamma0Rep p N hpN) g q
  rw [adjointGamma0Rep_units p N hpN] at h
  exact h.symm

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_sum_T_p_upper_LHS_dist_slot1_unfactor_diamond
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
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
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  congr 1
  exact slash_diamond_inv_T_p_upper_eq_T_p_lower_delta p hp hpN b
    (q.out : SL(2, ℤ)) f

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_upper_tile_shift_to_prefactored_of_FD_slash_exchange
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_FD_slash_exchange :
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
  rw [peterssonInner_sum_T_p_upper_residual_LHS_to_dist p hp hpN f g,
      peterssonInner_sum_T_p_upper_LHS_dist_slot2_to_sigma p hp hpN f g,
      peterssonInner_sum_T_p_upper_LHS_dist_slot1_unfactor_diamond p hp hpN f g]
  exact h_FD_slash_exchange

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_diamond_inv_α_eq_T_p_lower_via_matrix_factor
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (γ_α : SL(2, ℤ))
    (h_factor : ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) * α =
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) γ_α : GL (Fin 2) ℝ))
    (q : SL(2, ℤ)) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    ⇑g ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ_α) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  have h_diamond : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
      UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    show ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = _
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  rw [h_diamond, ← SlashAction.slash_mul, ← mul_assoc, h_factor]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_α_FD_slash_exchange_T_p_lower_form_of_canonical
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (γ_α : SL(2, ℤ))
    (h_factor : ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) * α =
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) γ_α : GL (Fin 2) ℝ))
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_canonical_α :
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
              (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
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
              (α *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          (⇑f ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ_α) *
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
            (α *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  rw [show (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ_α) *
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
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((Gamma1QuotEquivOfGamma0
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
              (adjointGamma0Rep p N hpN).property q).out :
              SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
    from Finset.sum_congr rfl fun q _ ↦ by
      congr 1
      exact (slash_diamond_inv_α_eq_T_p_lower_via_matrix_factor p hp hpN α γ_α
        h_factor (q.out : SL(2, ℤ)) f).symm]
  exact h_canonical_α

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_α_canonical_form_of_balanced
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_balanced :
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
              (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
            (⇑g ∣[k]
              (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
            (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
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
            (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  have h_LHS : (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((Gamma1QuotEquivOfGamma0
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
              (adjointGamma0Rep p N hpN).property q).out :
              SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) := by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    congr 1
    have h := slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv_GL
      (adjointGamma0Rep p N hpN) g q
    rw [adjointGamma0Rep_units p N hpN] at h
    exact h
  have h_RHS : (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k]
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((Gamma1QuotEquivOfGamma0
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
              (adjointGamma0Rep p N hpN).property q).out :
              SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
    set σ : SL(2, ℤ) ⧸ Gamma1 N ≃ SL(2, ℤ) ⧸ Gamma1 N :=
      Gamma1QuotEquivOfGamma0
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
        (adjointGamma0Rep p N hpN).property
    rw [← σ.sum_comp (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k]
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    congr 1
    have h := slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv_GL
      (adjointGamma0Rep p N hpN)
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) q
    rw [adjointGamma0Rep_units p N hpN] at h
    rw [h]
    congr 1
    show ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) = ⇑f
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
    rw [h_cancel]
  rw [h_LHS, h_balanced, h_RHS]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem balanced_α_of_aggregate_FD_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        ((α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        ((α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        ((α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj α) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj α) ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (h_FD_balance :
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj α) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj α) ⇑g) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) ∣[k]
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k]
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  have h_LHS_agg := peterssonInner_sum_slash_adjoint_coset_aggregate
    (k := k) α hα
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g))
    hd hm hint_LHS
  have h_RHS_agg :
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
          (⇑g ∣[k]
            (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj α) ⇑g := by
    rw [show (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
          (⇑g ∣[k]
            (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k
          ((α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            peterssonAdj α) ⇑g by
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [peterssonInner_slash_adjoint_coset_right (k := k) α hα
        (q.out : SL(2, ℤ))
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ⇑g, ← mul_smul]]
    exact (peterssonInner_iUnion_finite_aedisjoint
      (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
      hm hd
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k] peterssonAdj α)
      ⇑g hint_RHS).symm
  rw [h_LHS_agg, h_FD_balance, ← h_RHS_agg]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_FD_balance_of_post_swap_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_post_swap_balance :
      peterssonInner k
        (peterssonAdj α • ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k] α)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (peterssonAdj α • ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] α)) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
        peterssonAdj α) =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
        peterssonAdj α) ⇑g := by
  have hα_adj : 0 < (peterssonAdj α).det.val := by
    show 0 < ((peterssonAdj α).det : ℝˣ).val
    rw [peterssonAdj_det]
    exact hα
  rw [peterssonInner_slash_adjoint_right
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (peterssonAdj α) hα_adj
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g),
      peterssonAdj_peterssonAdj]
  rw [peterssonInner_slash_adjoint
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (peterssonAdj α) hα_adj
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ⇑g,
      peterssonAdj_peterssonAdj]
  exact h_post_swap_balance

open UpperHalfPlane in
private lemma peterssonAdj_mul_self_smul
    (β : GL (Fin 2) ℝ) (τ : ℍ) :
    ((peterssonAdj β * β : GL (Fin 2) ℝ) • τ : ℍ) = τ := by
  rw [mul_smul, peterssonAdj_smul_eq, inv_smul_smul]

open UpperHalfPlane in
/-- **T090 trivial action of `peterssonAdj β · β` on sets of `ℍ`.**

Set-level extension of `peterssonAdj_mul_self_smul`: pointwise triviality
implies `(peterssonAdj β · β) • S = S` for any `S : Set ℍ`. -/
lemma peterssonAdj_mul_self_smul_set
    (β : GL (Fin 2) ℝ) (S : Set ℍ) :
    ((peterssonAdj β * β : GL (Fin 2) ℝ) • S : Set ℍ) = S := by
  ext τ
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hs, hτ⟩
    have hτ' : (peterssonAdj β * β : GL (Fin 2) ℝ) • s = τ := hτ
    rw [peterssonAdj_mul_self_smul] at hτ'
    exact hτ' ▸ hs
  · intro hτ
    refine ⟨τ, hτ, ?_⟩
    show (peterssonAdj β * β : GL (Fin 2) ℝ) • τ = τ
    exact peterssonAdj_mul_self_smul β τ

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonAdj_smul_aggregate_tile_union_eq
    (α : GL (Fin 2) ℝ) :
    ((peterssonAdj α : GL (Fin 2) ℝ) • ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      ((α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) •
        (fd : Set ℍ)) : Set ℍ) =
    ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) := by
  rw [Set.smul_set_iUnion]
  congr 1
  funext q
  rw [← mul_smul, ← mul_assoc, mul_smul]
  exact peterssonAdj_mul_self_smul_set α _

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_post_swap_balance_of_SL_tile_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_SL_tile_balance :
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
        (⇑g ∣[k] α)) :
    peterssonInner k
      (peterssonAdj α • ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k] α)
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
    peterssonInner k
      (peterssonAdj α • ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
      (⇑g ∣[k] α) := by
  rw [peterssonAdj_smul_aggregate_tile_union_eq]
  exact h_SL_tile_balance

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_SL_tile_balance_of_post_swap_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_post_swap_balance :
      peterssonInner k
        (peterssonAdj α • ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k] α)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (peterssonAdj α • ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] α)) :
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
  rw [← peterssonAdj_smul_aggregate_tile_union_eq α]
  exact h_post_swap_balance

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_Gamma1_FD_eq_petN
    (F G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hd : Pairwise (fun q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))))
    (hint : IntegrableOn (fun τ ↦ petersson k ⇑F ⇑G τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp) :
    peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ))
        ⇑F ⇑G =
      petN F G := by
  rw [peterssonInner_iUnion_finite_aedisjoint _ hm hd _ _ hint]
  simp_rw [peterssonInner_mapGL_smul_eq_slash]
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_Gamma1_FD_diamond_unitary
    (F G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (d : (ZMod N)ˣ)
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hd : Pairwise (fun q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))))
    (hint_FG : IntegrableOn (fun τ ↦ petersson k ⇑F ⇑G τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_dFG : IntegrableOn
      (fun τ ↦ petersson k ⇑(diamondOp_cusp k d F) ⇑(diamondOp_cusp k d G) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp) :
    peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ))
        ⇑(diamondOp_cusp k d F) ⇑(diamondOp_cusp k d G) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ))
        ⇑F ⇑G := by
  rw [peterssonInner_Gamma1_FD_eq_petN (diamondOp_cusp k d F)
        (diamondOp_cusp k d G) hm hd hint_dFG,
      peterssonInner_Gamma1_FD_eq_petN F G hm hd hint_FG,
      diamondOp_petersson_unitary d F G]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_Gamma1_FD_diamond_slot_swap
    (F G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (d : (ZMod N)ˣ)
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hd : Pairwise (fun q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))))
    (hint_FG_inv : IntegrableOn
      (fun τ ↦ petersson k ⇑F ⇑(diamondOp_cusp k d⁻¹ G) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_dFG : IntegrableOn
      (fun τ ↦ petersson k ⇑(diamondOp_cusp k d F) ⇑G τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp) :
    peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ))
        ⇑(diamondOp_cusp k d F) ⇑G =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ))
        ⇑F ⇑(diamondOp_cusp k d⁻¹ G) := by
  rw [peterssonInner_Gamma1_FD_eq_petN (diamondOp_cusp k d F) G hm hd hint_dFG,
      peterssonInner_Gamma1_FD_eq_petN F (diamondOp_cusp k d⁻¹ G)
        hm hd hint_FG_inv]
  have h_cancel : diamondOp_cusp k d (diamondOp_cusp k d⁻¹ G) = G := by
    show diamondOpCusp k d (diamondOpCusp k d⁻¹ G) = G
    rw [show diamondOpCusp k d (diamondOpCusp k d⁻¹ G) =
        ((diamondOpCusp k d).comp (diamondOpCusp k d⁻¹)) G from rfl,
      ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
    rfl
  calc petN (diamondOp_cusp k d F) G
      = petN (diamondOp_cusp k d F) (diamondOp_cusp k d
          (diamondOp_cusp k d⁻¹ G)) := by rw [h_cancel]
    _ = petN F (diamondOp_cusp k d⁻¹ G) :=
        diamondOp_petersson_unitary d F (diamondOp_cusp k d⁻¹ G)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_M_infty_SL_tile_balance_iff_T_p_lower_diamond_form
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
    (peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))) := by
  rw [slash_diamond_inv_M_infty_eq_slash_T_p_lower_cusp p hp hpN f,
      slash_M_infty_eq_diamond_slash_T_p_lower_cusp_g p hp hpN g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_T_p_upper_SL_tile_balance_iff_T_p_lower_diamond_form
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
    (peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b))))) := by
  have h_LHS_slash :
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
        (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) =
      ⇑f ∣[k]
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b))) := by
    have h := slash_diamond_inv_T_p_upper_eq_T_p_lower_delta p hp hpN b 1 f
    simp only [inv_one, map_one, mul_one] at h
    exact h
  have h_RHS_slash :
      ⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) =
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b))) := by
    have h := slash_T_p_upper_eq_diamond_slash_T_p_lower_factor p hp hpN b g 1
    simp only [inv_one, map_one, mul_one] at h
    exact h
  rw [h_LHS_slash, h_RHS_slash]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_T_p_upper_SL_tile_balance_of_T_p_lower_diamond_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_diamond :
      peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑f ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b))))) :
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
        (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) :=
  (h_T_p_upper_SL_tile_balance_iff_T_p_lower_diamond_form p hp hpN b f g).mpr
    h_diamond

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_T_p_lower_diamond_form_iff_T_p_upper_zero_shifted_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))) ↔
    (peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ) • (fd : Set ℍ))
        ⇑f
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
      peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g))) := by
  have hα : 0 < ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)).det.val := by
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
  rw [peterssonInner_slash_adjoint (k := k) _ _ hα ⇑f
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g),
      peterssonInner_slash_adjoint_right (k := k) _ _ hα
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g),
      peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_M_infty_SL_tile_balance_iff_T_p_upper_zero_shifted_form
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
    (peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ) • (fd : Set ℍ))
        ⇑f
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
      peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g))) :=
  (h_M_infty_SL_tile_balance_iff_T_p_lower_diamond_form p hp hpN f g).trans
    (h_T_p_lower_diamond_form_iff_T_p_upper_zero_shifted_form p hp hpN f g)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_M_infty_SL_tile_balance_of_T_p_upper_zero_shifted_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_shifted :
      peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ) • (fd : Set ℍ))
          ⇑f
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
        peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g))) :
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
        (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) :=
  (h_M_infty_SL_tile_balance_iff_T_p_upper_zero_shifted_form p hp hpN f g).mpr
    h_shifted

open UpperHalfPlane ModularGroup MeasureTheory in
private def TpUpperZeroShiftedFormBlocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  peterssonInner k
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
        ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ))
      ⇑f
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
    peterssonInner k
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
        ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g))

open UpperHalfPlane ModularGroup MeasureTheory in
private def TpUpperBranchDiamondFormBlocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
      (⇑f ∣[k]
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b))))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_T_p_upper_SL_tile_balance_from_blocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : TpUpperBranchDiamondFormBlocker p hp hpN b f g) :
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
        (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) :=
  h_T_p_upper_SL_tile_balance_of_T_p_lower_diamond_form p hp hpN b f g h

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_M_infty_SL_tile_balance_from_blocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : TpUpperZeroShiftedFormBlocker p hp hpN f g) :
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
        (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) :=
  h_M_infty_SL_tile_balance_of_T_p_upper_zero_shifted_form p hp hpN f g h

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_M_infty_SL_tile_balance_via_double_adjoint_swap
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_post_adj_swap_balance :
      peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) =
      peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g) :
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
  rw [peterssonInner_slash_adjoint _ _
        (glMap_M_infty_det_pos N p hp.pos hpN)
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g),
      peterssonInner_slash_adjoint_right _ _
        (glMap_M_infty_det_pos N p hp.pos hpN)
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        ⇑g]
  exact h_post_adj_swap_balance

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem setIntegral_M_infty_shifted_SL_tile_union_via_GL_invariance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (h : ℍ → ℂ) :
    ∫ τ in (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)),
      h τ ∂μ_hyp =
    ∫ τ in ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ),
      h ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) • τ) ∂μ_hyp := by
  set α : GL(2, ℝ)⁺ := ⟨glMap (M_infty N p hp.pos hpN),
    glMap_M_infty_det_pos N p hp.pos hpN⟩
  rw [show ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) •
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) =
      (fun τ ↦ α • τ) ''
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
    by rw [Set.image_smul]; rfl]
  exact (measurePreserving_smul α μ_hyp).setIntegral_image_emb
    (measurableEmbedding_const_smul α) _ _

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem post_swap_balance_via_GL_change_of_variables
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_UNION_translated_balance :
      ∫ τ in ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ),
        petersson k
          ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) • τ) ∂μ_hyp =
      ∫ τ in ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ),
        petersson k
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
          ⇑g
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) • τ) ∂μ_hyp) :
    peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) =
    peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g := by
  show ∫ τ in (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)),
        petersson k
          ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ
          ∂μ_hyp =
      ∫ τ in (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)),
        petersson k
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
          ⇑g τ
          ∂μ_hyp
  rw [setIntegral_M_infty_shifted_SL_tile_union_via_GL_invariance p hp hpN
        (petersson k
          ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))),
      setIntegral_M_infty_shifted_SL_tile_union_via_GL_invariance p hp hpN
        (petersson k
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
          ⇑g)]
  exact h_UNION_translated_balance

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_M_infty_tile_shift_to_prefactored_from_SL_tile_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (h_M_infty_SL_tile_balance :
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
        (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))) :
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
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) :=
  h_M_infty_tile_shift_to_prefactored_of_FD_slash_exchange p hp hpN f g
    (h_α_FD_slash_exchange_T_p_lower_form_of_canonical p hp hpN
      (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
      (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
        M_infty_Gamma1_factor N p hpN 0)
      (mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon N p hp.pos hpN)
      f g
      (h_α_canonical_form_of_balanced p hp hpN
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) f g
        (balanced_α_of_aggregate_FD_balance p hp hpN
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          (glMap_M_infty_det_pos N p hp.pos hpN) f g
          hd hm hint_LHS hint_RHS
          (h_FD_balance_of_post_swap_balance p hp hpN
            (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
            (glMap_M_infty_det_pos N p hp.pos hpN) f g
            (h_post_swap_balance_of_SL_tile_balance p hp hpN
              (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
              (glMap_M_infty_det_pos N p hp.pos hpN) f g
              h_M_infty_SL_tile_balance)))))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_M_infty_tile_shift_to_prefactored_from_blocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (h_blocker : TpUpperZeroShiftedFormBlocker p hp hpN f g) :
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
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) :=
  h_M_infty_tile_shift_to_prefactored_from_SL_tile_balance p hp hpN f g
    hd hm hint_LHS hint_RHS
    (h_M_infty_SL_tile_balance_from_blocker p hp hpN f g h_blocker)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_M_infty_FD_slash_exchange_from_SL_tile_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (h_M_infty_SL_tile_balance :
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
        (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))) :
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
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) :=
  h_α_FD_slash_exchange_T_p_lower_form_of_canonical p hp hpN
    (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
    (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
      M_infty_Gamma1_factor N p hpN 0)
    (mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon N p hp.pos hpN)
    f g
    (h_α_canonical_form_of_balanced p hp hpN
      (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) f g
      (balanced_α_of_aggregate_FD_balance p hp hpN
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        (glMap_M_infty_det_pos N p hp.pos hpN) f g
        hd hm hint_LHS hint_RHS
        (h_FD_balance_of_post_swap_balance p hp hpN
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          (glMap_M_infty_det_pos N p hp.pos hpN) f g
          (h_post_swap_balance_of_SL_tile_balance p hp hpN
            (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
            (glMap_M_infty_det_pos N p hp.pos hpN) f g
            h_M_infty_SL_tile_balance))))

private theorem glMap_T_p_upper_det_pos (p : ℕ) (hp : 0 < p) (b : ℕ) :
    0 < (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ).det.val := by
  show 0 < ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ).det
  rw [show ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
  rw [show (((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
      (algebraMap ℚ ℝ) (((T_p_upper p hp b : GL (Fin 2) ℚ).val).det) from
        (RingHom.map_det _ _).symm]
  rw [show ((T_p_upper p hp b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
    simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.det_fin_two, Matrix.of_apply]]
  show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
  rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
  exact_mod_cast hp

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **LHS-aggregate-as-tile-form** (Step 2 (in progress) of T205-d-SYMM chain,
2026-05-11). Expresses `petN(T_p f, g)` as a sum over `(q, β)` of
`β`-translated tile integrals over `fd`, where `β` ranges over the Hecke
representatives `{glMap M_∞} ∪ {glMap T_p_upper(b)}_{b<p}` and `q` ranges over
`SL(2, ℤ) ⧸ Γ₁(N)`. -/
theorem petN_heckeT_p_LHS_as_tile_aggregate
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
            (((q.out : SL(2, ℤ))⁻¹ : SL(2, ℤ)) • (fd : Set ℍ)))
          ⇑f
          ((⇑g : ℍ → ℂ) ∣[k]
            peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        + ∑ b ∈ Finset.range p,
            peterssonInner k
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
                (((q.out : SL(2, ℤ))⁻¹ : SL(2, ℤ)) • (fd : Set ℍ)))
              ⇑f
              ((⇑g : ℍ → ℂ) ∣[k]
                peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) := by
  rw [petN_T_p_heckeT_p_LHS_sum_distributed p hp hpN f g]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  · exact peterssonInner_LHS_distributed_summand_to_tile_form q
      (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
      (glMap_M_infty_det_pos N p hp.pos hpN) f g
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    exact peterssonInner_LHS_distributed_summand_to_tile_form q
      (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
      (glMap_T_p_upper_det_pos p hp.pos b) f g

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **LHS-aggregate-as-tile-form with per-β g-slot identifications**. -/
theorem petN_heckeT_p_LHS_as_tile_aggregate_g_slot_simplified
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
            (((q.out : SL(2, ℤ))⁻¹ : SL(2, ℤ)) • (fd : Set ℍ)))
          ⇑f
          (((⇑g : ℍ → ℂ) ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (sigma_p_specific N p hp.pos hpN)⁻¹))
        + ∑ b ∈ Finset.range p,
            peterssonInner k
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
                (((q.out : SL(2, ℤ))⁻¹ : SL(2, ℤ)) • (fd : Set ℍ)))
              ⇑f
              ((⇑g : ℍ → ℂ) ∣[k]
                (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))) := by
  rw [petN_heckeT_p_LHS_as_tile_aggregate p hp hpN f g]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  ·
    rw [peterssonAdj_glMap_M_infty_eq N p hp.pos hpN, SlashAction.slash_mul]
  ·
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [slash_peterssonAdj_T_p_upper_eq_T_p_lower p hp hpN b g]

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
private theorem petN_heckeT_p_adjoint_standard_form_via_sum_chain
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

/-! ### Helper lemmas for `heckeT_n_adjoint` -/

private theorem heckeT_n_cusp_comm_diamondOp (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp k n (diamondOp_cusp k d f) =
      diamondOp_cusp k d (heckeT_n_cusp k n f) := by
  apply CuspForm.ext; intro τ
  show ((heckeT_n k n) (diamondOp k d f.toModularForm')).toFun τ =
    ((diamondOp k d) (heckeT_n k n f.toModularForm')).toFun τ
  have h := congr_fun (congr_arg DFunLike.coe (heckeT_n_comm_diamondOp k n hn d))
    f.toModularForm'
  simp only [Module.End.mul_apply] at h
  exact congr_arg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k ↦ m.toFun τ) h.symm

private theorem heckeT_n_cusp_decomp (m : ℕ) [NeZero m] (hm : 1 < m)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    let p := m.minFac
    let hp := Nat.minFac_prime (by omega : m ≠ 1)
    let v := m.factorization p
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    haveI : NeZero (m / p ^ v) :=
      ⟨(Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p))
        (pow_pos hp.pos v)).ne'⟩
    heckeT_n_cusp k m f =
      heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k (m / p ^ v) f) := by
  apply CuspForm.ext; intro z
  exact heckeT_n_cusp_unfold m hm f z

private theorem heckeT_n_cusp_comm (m n : ℕ) [NeZero m] [NeZero n]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp k m (heckeT_n_cusp k n f) =
      heckeT_n_cusp k n (heckeT_n_cusp k m f) := by
  apply CuspForm.ext; intro τ
  show ((heckeT_n k m) ((heckeT_n k n) f.toModularForm')).toFun τ =
    ((heckeT_n k n) ((heckeT_n k m) f.toModularForm')).toFun τ
  have h := congr_fun (congr_arg DFunLike.coe (heckeT_n_comm k m n)) f.toModularForm'
  simp only [Module.End.mul_apply] at h
  exact congr_arg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k ↦ m.toFun τ) h

private theorem diamondOp_cusp_comp (d₁ d₂ : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d₁ (diamondOp_cusp k d₂ f) =
      diamondOp_cusp k (d₁ * d₂) f := by
  show diamondOpCusp k d₁ (diamondOpCusp k d₂ f) = diamondOpCusp k (d₁ * d₂) f
  rw [show diamondOpCusp k d₁ (diamondOpCusp k d₂ f) =
    ((diamondOpCusp k d₁).comp (diamondOpCusp k d₂)) f from rfl,
    ← diamondOpCusp_mul]

private theorem diamondOp_cusp_one
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k (1 : (ZMod N)ˣ) f = f := by
  show diamondOpCusp k 1 f = f
  have := congr_fun (congr_arg DFunLike.coe (diamondOpCusp_one (N := N) (k := k))) f
  exact CuspForm.ext fun τ ↦ congr_arg (fun m ↦ m τ) this

private theorem heckeT_n_adjoint_coprime_case (m : ℕ) [NeZero m]
    (hcop : Nat.Coprime m N) (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    (hn₁_cop : Nat.Coprime n₁ N) (hn₂_cop : Nat.Coprime n₂ N)
    (hpv_dvd : n₁ ∣ m) (hdiv_eq : n₂ = m / n₁)
    (hDecomp : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        heckeT_n_cusp k m h =
          heckeT_n_cusp k n₁ (heckeT_n_cusp k n₂ h))
    (ih_n₁ : ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        petN (heckeT_n_cusp k n₁ f₀) g₀ =
          petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹
            (heckeT_n_cusp k n₁ g₀)))
    (ih_n₂ : ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        petN (heckeT_n_cusp k n₂ f₀) g₀ =
          petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime n₂ hn₂_cop)⁻¹
            (heckeT_n_cusp k n₂ g₀)))
    (f' g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_n_cusp k m f') g' =
      petN f' (diamondOp_cusp k (ZMod.unitOfCoprime m hcop)⁻¹
        (heckeT_n_cusp k m g')) := by
  rw [hDecomp f']
  rw [ih_n₁ (heckeT_n_cusp k n₂ f') g']
  rw [ih_n₂ f' (diamondOp_cusp k (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹
    (heckeT_n_cusp k n₁ g'))]
  rw [heckeT_n_cusp_comm_diamondOp n₂ hn₂_cop
    (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹ (heckeT_n_cusp k n₁ g')]
  rw [diamondOp_cusp_comp]
  have h_hecke : heckeT_n_cusp k n₂ (heckeT_n_cusp k n₁ g') = heckeT_n_cusp k m g' :=
    (heckeT_n_cusp_comm n₂ n₁ g').trans (hDecomp g').symm
  have h_unit : (ZMod.unitOfCoprime n₂ hn₂_cop)⁻¹ * (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹ =
      (ZMod.unitOfCoprime m hcop)⁻¹ := by
    rw [← mul_inv]; congr 1; ext
    simp only [Units.val_mul, ZMod.coe_unitOfCoprime]; rw [mul_comm]
    exact_mod_cast congr_arg (Nat.cast (R := ZMod N))
      (show (n₁ : ℕ) * n₂ = m by rw [hdiv_eq]; exact Nat.mul_div_cancel' hpv_dvd)
  simp only [h_hecke, h_unit]

private theorem heckeT_n_cusp_ppow_recursion (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
    haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
    haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
    heckeT_n_cusp k (p ^ (r + 2)) f =
      heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) f) -
        (↑p : ℂ) ^ (k - 1) • diamondOp_cusp k (ZMod.unitOfCoprime p hpN)
          (heckeT_n_cusp k (p ^ r) f) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
  apply CuspForm.ext; intro τ
  show (heckeT_n k (p ^ (r + 2)) f.toModularForm').toFun τ =
    ((heckeT_n k p) ((heckeT_n k (p ^ (r + 1))) f.toModularForm')).toFun τ -
      (↑p : ℂ) ^ (k - 1) •
        ((diamondOp k (ZMod.unitOfCoprime p hpN))
          ((heckeT_n k (p ^ r)) f.toModularForm')).toFun τ
  rw [heckeT_n_prime_pow k hp (r + 2) (by omega), heckeT_n_prime_pow k hp (r + 1) (by omega),
      heckeT_n_prime_coprime k hp hpN]
  rw [heckeT_ppow_succ_succ k p hp r]
  rw [diamondOp_ext_coprime k hpN, heckeT_p_all_coprime k hp hpN]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply]
  conv_rhs =>
    rw [show heckeT_n k (p ^ r) = heckeT_ppow (N := N) k p hp r by
        rcases r with _ | r
        · simp [heckeT_n, heckeT_n_aux, heckeT_ppow]
        · exact heckeT_n_prime_pow k hp _ (by omega)]
  rfl

private theorem diamondOp_cusp_cancel (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d (diamondOp_cusp k d⁻¹ f) = f := by
  show diamondOpCusp k d (diamondOpCusp k d⁻¹ f) = f
  rw [show diamondOpCusp k d (diamondOpCusp k d⁻¹ f) =
      ((diamondOpCusp k d).comp (diamondOpCusp k d⁻¹)) f from rfl,
    ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
  rfl

private theorem diamondOp_cusp_inv_cancel (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d⁻¹ (diamondOp_cusp k d f) = f := by
  show diamondOpCusp k d⁻¹ (diamondOpCusp k d f) = f
  rw [show diamondOpCusp k d⁻¹ (diamondOpCusp k d f) =
      ((diamondOpCusp k d⁻¹).comp (diamondOpCusp k d)) f from rfl,
    ← diamondOpCusp_mul, inv_mul_cancel, diamondOpCusp_one]
  rfl

private theorem petN_diamondOp_adjoint (d : (ZMod N)ˣ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k d f) g =
      petN f (diamondOp_cusp k d⁻¹ g) := by
  calc petN (diamondOp_cusp k d f) g
      = petN (diamondOp_cusp k d f) (diamondOp_cusp k d (diamondOp_cusp k d⁻¹ g)) := by
        rw [diamondOp_cusp_cancel]
    _ = petN f (diamondOp_cusp k d⁻¹ g) := diamondOp_petersson_unitary d f _

private theorem conj_natCast_zpow (p : ℕ) : starRingEnd ℂ ((↑p : ℂ) ^ (k - 1)) =
    (↑p : ℂ) ^ (k - 1) := by
  have : starRingEnd ℂ (↑p : ℂ) = (↑p : ℂ) := by
    rw [show (↑p : ℂ) = (↑(p : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.conj_ofReal _
  rw [map_zpow₀, this]

private theorem heckeT_n_adjoint_ppow_case
    (p : ℕ) (hp : Nat.Prime p) (v : ℕ) (hv : 2 ≤ v)
    (hcop : Nat.Coprime (p ^ v) N)
    (ih : ∀ j : ℕ, j < p ^ v → (hj_pos : 0 < j) → (hj : Nat.Coprime j N) →
      ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        haveI : NeZero j := ⟨hj_pos.ne'⟩
        petN (heckeT_n_cusp k j f₀) g₀ =
          petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime j hj)⁻¹
            (heckeT_n_cusp k j g₀)))
    (f' g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    petN (heckeT_n_cusp k (p ^ v) f') g' =
      petN f' (diamondOp_cusp k (ZMod.unitOfCoprime (p ^ v) hcop)⁻¹
        (heckeT_n_cusp k (p ^ v) g')) := by
  haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
  obtain ⟨r, rfl⟩ : ∃ r, v = r + 2 := ⟨v - 2, by omega⟩
  have hp_cop : Nat.Coprime p N := Nat.Coprime.coprime_dvd_left
    (dvd_pow_self p (by omega : r + 2 ≠ 0)) hcop
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
  have hpv1_cop : Nat.Coprime (p ^ (r + 1)) N := Nat.Coprime.pow_left _ hp_cop
  have hpr_cop : Nat.Coprime (p ^ r) N := Nat.Coprime.pow_left _ hp_cop
  have hp_lt : p < p ^ (r + 2) := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ (r + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hpv1_lt : p ^ (r + 1) < p ^ (r + 2) :=
    Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hpr_lt : p ^ r < p ^ (r + 2) :=
    Nat.pow_lt_pow_right hp.one_lt (by omega : r < r + 2)
  set up := ZMod.unitOfCoprime p hp_cop
  set c := (↑p : ℂ) ^ (k - 1)
  rw [heckeT_n_cusp_ppow_recursion p hp hp_cop r f']
  rw [show (heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) f') -
      c • diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) f') :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) f') +
      (-(c • diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) f'))) from sub_eq_add_neg _ _]
  rw [petN_add_left, petN_neg_left, petN_conj_smul_left, conj_natCast_zpow]
  rw [ih p hp_lt hp.pos hp_cop (heckeT_n_cusp k (p ^ (r + 1)) f') g']
  rw [ih (p ^ (r + 1)) hpv1_lt (pow_pos hp.pos _) hpv1_cop f'
    (diamondOp_cusp k up⁻¹ (heckeT_n_cusp k p g'))]
  rw [petN_diamondOp_adjoint up (heckeT_n_cusp k (p ^ r) f') g']
  rw [ih (p ^ r) hpr_lt (pow_pos hp.pos _) hpr_cop f'
    (diamondOp_cusp k up⁻¹ g')]
  rw [heckeT_n_cusp_comm_diamondOp (p ^ (r + 1)) hpv1_cop up⁻¹
      (heckeT_n_cusp k p g')]
  rw [heckeT_n_cusp_comm_diamondOp (p ^ r) hpr_cop up⁻¹ g']
  rw [diamondOp_cusp_comp, diamondOp_cusp_comp]
  rw [heckeT_n_cusp_comm (p ^ (r + 1)) p g']
  rw [← petN_smul_right c f', ← petN_neg_right, ← petN_add_right]
  congr 1
  have h_unit_prod_v : (ZMod.unitOfCoprime (p ^ (r + 1)) hpv1_cop)⁻¹ * up⁻¹ =
      (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹ := by
    rw [← mul_inv]; congr 1; ext
    simp only [Units.val_mul, ZMod.coe_unitOfCoprime, up]
    push_cast; ring
  have h_unit_prod_vm1 : (ZMod.unitOfCoprime (p ^ r) hpr_cop)⁻¹ * up⁻¹ =
      (ZMod.unitOfCoprime (p ^ (r + 1)) hpv1_cop)⁻¹ := by
    rw [← mul_inv]; congr 1; ext
    simp only [Units.val_mul, ZMod.coe_unitOfCoprime, up]
    push_cast; ring
  rw [h_unit_prod_v, h_unit_prod_vm1]
  rw [heckeT_n_cusp_ppow_recursion p hp hp_cop r g']
  rw [show diamondOp_cusp k (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹
      (heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) g') -
        c • diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) g')) =
      diamondOp_cusp k (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹
        (heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) g')) -
      diamondOp_cusp k (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹
        (c • diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) g')) by
    show diamondOpCusp k _ _ = diamondOpCusp k _ _ - diamondOpCusp k _ _
    rw [← (diamondOpCusp k _).map_sub]]
  rw [show diamondOp_cusp k (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹
      (c • diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) g')) =
      c • diamondOp_cusp k (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹
        (diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) g')) by
    show diamondOpCusp k _ _ = c • diamondOpCusp k _ _
    rw [← (diamondOpCusp k _).map_smul]]
  rw [diamondOp_cusp_comp]
  have h_unit_cancel : (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹ * up =
      (ZMod.unitOfCoprime (p ^ (r + 1)) hpv1_cop)⁻¹ := by
    have := h_unit_prod_v
    calc (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹ * up
        = (ZMod.unitOfCoprime (p ^ (r + 1)) hpv1_cop)⁻¹ * up⁻¹ * up := by
          rw [this]
      _ = (ZMod.unitOfCoprime (p ^ (r + 1)) hpv1_cop)⁻¹ * (up⁻¹ * up) := by
          rw [mul_assoc]
      _ = (ZMod.unitOfCoprime (p ^ (r + 1)) hpv1_cop)⁻¹ := by
          rw [inv_mul_cancel, mul_one]
  rw [h_unit_cancel]
  abel

/-! ### Normality of Hecke operators -/

/-- The Hecke adjoint for general T_n: `T_n* = ⟨n⟩⁻¹ T_n` on `S_k(Γ₁(N))`,
w.r.t. the level-N Petersson inner product `petN`. -/
theorem heckeT_n_adjoint
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_n_cusp k n f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹
        (heckeT_n_cusp k n g)) := by
  suffices key : ∀ m : ℕ, (hm : 0 < m) → (hcop : Nat.Coprime m N) →
      ∀ f' g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        haveI : NeZero m := ⟨hm.ne'⟩
        petN (heckeT_n_cusp k m f') g' =
          petN f' (diamondOp_cusp k (ZMod.unitOfCoprime m hcop)⁻¹
            (heckeT_n_cusp k m g')) from
    key n (NeZero.pos n) hn f g
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hcop f' g'
    haveI instm : NeZero m := ⟨hm.ne'⟩
    by_cases hle : m ≤ 1
    ·
      have hm1 : m = 1 := by omega
      subst hm1
      have hT1f : heckeT_n_cusp (N := N) k 1 f' = f' := CuspForm.ext fun τ ↦ by
        show (heckeT_n k 1 f'.toModularForm').toFun τ = f' τ; rw [heckeT_n_one]; rfl
      have hT1g : heckeT_n_cusp (N := N) k 1 g' = g' := CuspForm.ext fun τ ↦ by
        show (heckeT_n k 1 g'.toModularForm').toFun τ = g' τ; rw [heckeT_n_one]; rfl
      have hunit : ZMod.unitOfCoprime 1 hcop = 1 := by
        ext; simp [ZMod.coe_unitOfCoprime]
      rw [hT1f, hT1g, hunit, inv_one, diamondOp_cusp_one]
    ·
      push_neg at hle
      set p := m.minFac with hp_def
      have hpp : p.Prime := Nat.minFac_prime (by omega : m ≠ 1)
      set v := m.factorization p with hv_def
      have hv_pos : 0 < v := hpp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)
      have hpv_pos : 0 < p ^ v := pow_pos hpp.pos v
      have hdiv_pos : 0 < m / p ^ v :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) hpv_pos
      have hdiv_lt : m / p ^ v < m := heckeT_n_unfold_lt m hle
      haveI : NeZero (p ^ v) := ⟨hpv_pos.ne'⟩
      haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
      have hpv_cop : Nat.Coprime (p ^ v) N := Nat.Coprime.pow_left v
        (Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd m) hcop)
      have hdiv_cop : Nat.Coprime (m / p ^ v) N :=
        Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m p)) hcop
      have hDecomp : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
          heckeT_n_cusp k m h =
            heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k (m / p ^ v) h) :=
        fun h ↦ heckeT_n_cusp_decomp m hle h
      have ih_div : ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
          petN (heckeT_n_cusp k (m / p ^ v) f₀) g₀ =
            petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime (m / p ^ v) hdiv_cop)⁻¹
              (heckeT_n_cusp k (m / p ^ v) g₀)) :=
        fun f₀ g₀ ↦ ih _ hdiv_lt hdiv_pos hdiv_cop f₀ g₀
      by_cases hpv_lt : p ^ v < m
      ·
        have ih_pv : ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
            petN (heckeT_n_cusp k (p ^ v) f₀) g₀ =
              petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime (p ^ v) hpv_cop)⁻¹
                (heckeT_n_cusp k (p ^ v) g₀)) :=
          fun f₀ g₀ ↦ ih _ hpv_lt hpv_pos hpv_cop f₀ g₀
        exact heckeT_n_adjoint_coprime_case m hcop (p ^ v) (m / p ^ v)
          hpv_cop hdiv_cop (Nat.ordProj_dvd m p) rfl hDecomp ih_pv ih_div f' g'
      ·
        have hpv_eq : p ^ v = m := le_antisymm
          (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (not_lt.mp hpv_lt)
        by_cases hv1 : v = 1
        ·
          have hp_m : Nat.Prime m := by rw [← hpv_eq, hv1, pow_one]; exact hpp
          have hTn_eq : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
              heckeT_n_cusp k m h = heckeT_p_cusp k m hp_m hcop h :=
            fun h ↦ CuspForm.ext fun τ ↦ by
              show (heckeT_n k m h.toModularForm').toFun τ =
                (heckeT_p k m hp_m hcop h.toModularForm').toFun τ
              rw [heckeT_n_prime_coprime k hp_m hcop]
          rw [hTn_eq f', hTn_eq g']
          exact heckeT_p_adjoint m hp_m hcop f' g'
        ·
          have hv2 : 2 ≤ v := by omega
          have hTn_pv : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
              heckeT_n_cusp k m h = heckeT_n_cusp k (p ^ v) h := fun h ↦ CuspForm.ext fun τ ↦ by
              show (heckeT_n k m h.toModularForm').toFun τ =
                (heckeT_n k (p ^ v) h.toModularForm').toFun τ
              simp only [heckeT_n, hpv_eq]
          have h_unit_eq : (ZMod.unitOfCoprime m hcop)⁻¹ =
              (ZMod.unitOfCoprime (p ^ v) hpv_cop)⁻¹ := by
            congr 1; ext; simp [ZMod.coe_unitOfCoprime, hpv_eq]
          rw [hTn_pv f', hTn_pv g', h_unit_eq]
          exact heckeT_n_adjoint_ppow_case p hpp v hv2 hpv_cop
            (fun j hj hj_pos hj_cop f₀ g₀ ↦ by
              haveI : NeZero j := ⟨hj_pos.ne'⟩
              exact ih j (hpv_eq ▸ hj) hj_pos hj_cop f₀ g₀) f' g'

/-- T_n is normal: `T_n T_n* = T_n* T_n` for `(n,N) = 1`.

Since `T_n* = ⟨n⟩⁻¹ T_n` and `T_n` commutes with `⟨n⟩` (proved by
`heckeT_n_comm_diamondOp`), normality reduces to function-level commutativity.

Reference: [DS] Theorem 5.5.4, [Miy] Theorem 4.5.5. -/
theorem heckeT_n_normal
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp k n (diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹
      (heckeT_n_cusp k n f)) =
    diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹
      (heckeT_n_cusp k n (heckeT_n_cusp k n f)) := by
  have hToModT : ∀ (h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      (heckeT_n_cusp k n h).toModularForm' = heckeT_n k n h.toModularForm' := by
    intro h; apply DFunLike.ext; intro τ; rfl
  have hToModD : ∀ (h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      (diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹ h).toModularForm' =
        diamondOp k (ZMod.unitOfCoprime n hn)⁻¹ h.toModularForm' := by
    intro h; apply DFunLike.ext; intro τ; rfl
  apply DFunLike.ext
  intro τ
  show ((heckeT_n k n) (diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹
    (heckeT_n_cusp k n f)).toModularForm').toFun τ =
      ((diamondOp k (ZMod.unitOfCoprime n hn)⁻¹)
        (heckeT_n_cusp k n (heckeT_n_cusp k n f)).toModularForm').toFun τ
  rw [hToModD, hToModT, hToModT, hToModT]
  have h := congr_fun (congr_arg DFunLike.coe
    (heckeT_n_comm_diamondOp k n hn (ZMod.unitOfCoprime n hn)⁻¹).symm)
    (heckeT_n k n f.toModularForm')
  simp only [Module.End.mul_apply] at h
  exact congr_arg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k ↦ m.toFun τ) h

/-! ### Simultaneous eigenform basis -/

/-- A cusp form is a common eigenfunction of all `T_n` (cusp form version). -/
abbrev IsCommonEigenfunctionCusp (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∀ n : ℕ+, Nat.Coprime n.val N →
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    ∃ a : ℂ, heckeT_n_cusp k n.val f = a • f

/-- `heckeT_n_cusp` preserves the cusp-form character space `S_k(Γ₁(N), χ)`.
Follows from `heckeT_n_preserves_charSpace` (the `ModularForm` version) via
the cusp-form coercion. -/
lemma heckeT_n_cusp_preserves_cuspFormCharSpace
    (k : ℤ) (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeT_n_cusp k n f ∈ cuspFormCharSpace k χ := by
  rw [mem_cuspFormCharSpace_iff] at hf ⊢
  intro d
  show diamondOpCusp k d (heckeT_n_cusp k n f) = (↑(χ d) : ℂ) • heckeT_n_cusp k n f
  have h_comm : diamondOpCusp k d (heckeT_n_cusp k n f) =
      heckeT_n_cusp k n (diamondOpCusp k d f) := by
    ext z
    show ((diamondOp k d) (heckeT_n k n f.toModularForm')).toFun z =
      ((heckeT_n k n) (diamondOp k d f.toModularForm')).toFun z
    have h := DFunLike.congr_fun (heckeT_n_comm_diamondOp k n hn d) f.toModularForm'
    simp only [Module.End.mul_apply] at h
    exact congr_arg (fun m : ModularForm _ _ ↦ m.toFun z) h
  rw [h_comm]
  show heckeT_n_cusp k n (diamondOpCusp k d f) = ↑(χ d) • heckeT_n_cusp k n f
  have hfd : diamondOpCusp k d f = (↑(χ d) : ℂ) • f := hf d
  rw [hfd]
  ext z
  show (heckeT_n k n ((↑(χ d) : ℂ) • f).toModularForm').toFun z =
    (↑(χ d) : ℂ) • (heckeT_n k n f.toModularForm').toFun z
  rw [show ((↑(χ d) : ℂ) • f).toModularForm' = (↑(χ d) : ℂ) • f.toModularForm' from rfl, map_smul]
  rfl

/-- `T_n` restricted to `cuspFormCharSpace` as a linear endomorphism. -/
noncomputable def heckeT_n_cusp_charRestrict
    (k : ℤ) (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (cuspFormCharSpace k χ) where
  toFun := fun ⟨f, hf⟩ ↦ ⟨heckeT_n_cusp k n f, heckeT_n_cusp_preserves_cuspFormCharSpace k n hn χ hf⟩
  map_add' := fun ⟨f₁, _⟩ ⟨f₂, _⟩ ↦ by
    ext z; show (heckeT_n k n (f₁ + f₂).toModularForm').toFun z =
      ((heckeT_n k n f₁.toModularForm').toFun z + (heckeT_n k n f₂.toModularForm').toFun z)
    rw [show (f₁ + f₂).toModularForm' = f₁.toModularForm' + f₂.toModularForm' from rfl, map_add]
    rfl
  map_smul' := fun c ⟨f, _⟩ ↦ by
    ext z; show (heckeT_n k n (c • f).toModularForm').toFun z =
      c • (heckeT_n k n f.toModularForm').toFun z
    rw [show (c • f).toModularForm' = c • f.toModularForm' from rfl, map_smul]
    rfl

private theorem petN_add_left'
    (f₁ f₂ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (f₁ + f₂) g = petN f₁ g + petN f₂ g := by
  have h := petN_add_right g f₁ f₂
  have e := congr_arg (starRingEnd ℂ) h
  rw [petN_conj_symm, map_add, petN_conj_symm, petN_conj_symm] at e
  exact e

private theorem petN_conj_smul_left'
    (c : ℂ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (c • f) g = starRingEnd ℂ c * petN f g := by
  simp only [petN, Finset.mul_sum]
  congr 1; ext q
  have hcoe : ⇑(c • f) = c • ⇑f := rfl
  have h1 : ⇑(c • f) ∣[k] (q.out : SL(2, ℤ))⁻¹ = c • (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹) := by
    rw [hcoe]
    exact ModularForm.SL_smul_slash k _ ⇑f c
  rw [h1]
  exact UpperHalfPlane.peterssonInner_conj_smul_left k ModularGroup.fd c _ _

/-- `petN f f` has non-negative real part. Each summand is a non-negative real
(by `petN_summand_nonneg`), so the sum is too. -/
lemma petN_self_re_nonneg (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    0 ≤ (petN f f).re := by
  simp only [petN, Complex.re_sum]
  apply Finset.sum_nonneg
  intro q _
  obtain ⟨r, hr_nonneg, hr_eq⟩ := petN_summand_nonneg f q
  rw [hr_eq, Complex.ofReal_re]
  exact hr_nonneg

/-- An `InnerProductSpace.Core` instance on `CuspForm` from `petN`.

This provides the algebraic inner product structure needed for the spectral theorem.
The inner product is `⟪f, g⟫ := petN f g` (conjugate-linear in first, linear in second). -/
noncomputable def petN_innerProductCore :
    @InnerProductSpace.Core ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) _ _ _ where
  inner f g := petN f g
  conj_inner_symm f g := by
    show starRingEnd ℂ (petN g f) = petN f g
    exact petN_conj_symm f g
  re_inner_nonneg f := petN_self_re_nonneg f
  add_left f g h := petN_add_left' f g h
  smul_left f g c := petN_conj_smul_left' c f g
  definite f hf := petN_definite f hf

private lemma heckeT_n_adjoint_on_charSpace
    (χ : (ZMod N)ˣ →* ℂˣ)
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) (hg : g ∈ cuspFormCharSpace k χ) :
    petN (heckeT_n_cusp k n f) g =
      (↑(χ (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * petN f (heckeT_n_cusp k n g) := by
  rw [heckeT_n_adjoint n hn f g]
  have hTg : heckeT_n_cusp k n g ∈ cuspFormCharSpace k χ :=
    heckeT_n_cusp_preserves_cuspFormCharSpace k n hn χ hg
  have h_diamond : diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeT_n_cusp k n g) =
      (↑(χ (ZMod.unitOfCoprime n hn)⁻¹) : ℂ) • heckeT_n_cusp k n g := by
    exact ((mem_cuspFormCharSpace_iff k χ _).mp hTg) (ZMod.unitOfCoprime n hn)⁻¹
  rw [h_diamond]
  simp only [map_inv, Units.val_inv_eq_inv_val]
  exact petN_smul_right _ f (heckeT_n_cusp k n g)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T024 public Hecke `T_p` adjoint on character space (sum-chain route).** -/
theorem petN_heckeT_p_adjoint_on_charSpace_via_sum_chain
    (χ : (ZMod N)ˣ →* ℂˣ) (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) (hg : g ∈ cuspFormCharSpace k χ)
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
                      SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) ) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      (↑(χ (ZMod.unitOfCoprime p hpN))⁻¹ : ℂ) *
        petN f (heckeT_p_cusp k p hp hpN g) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hT_p_eq_T_n : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      heckeT_n_cusp k p h = heckeT_p_cusp k p hp hpN h :=
    fun h ↦ CuspForm.ext fun τ ↦ by
      show (heckeT_n k p h.toModularForm').toFun τ =
        (heckeT_p k p hp hpN h.toModularForm').toFun τ
      rw [heckeT_n_prime_coprime k hp hpN]
  have h_unsymm := petN_heckeT_p_adjoint_standard_form_via_sum_chain p hp hpN f g
    h_LHS_dist_eq_RHS_absorbed
  rw [h_unsymm, ← hT_p_eq_T_n g]
  have hTng : heckeT_n_cusp k p g ∈ cuspFormCharSpace k χ :=
    heckeT_n_cusp_preserves_cuspFormCharSpace k p hpN χ hg
  have h_diamond : diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (heckeT_n_cusp k p g) =
      (↑(χ (ZMod.unitOfCoprime p hpN)⁻¹) : ℂ) • heckeT_n_cusp k p g :=
    ((mem_cuspFormCharSpace_iff k χ _).mp hTng) (ZMod.unitOfCoprime p hpN)⁻¹
  rw [h_diamond, hT_p_eq_T_n g]
  simp only [map_inv, Units.val_inv_eq_inv_val]
  exact petN_smul_right _ f (heckeT_p_cusp k p hp hpN g)

private lemma heckeT_n_cusp_isSemisimple_on_charSpace
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)]
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) :
    ⨆ μ : ℂ, (heckeT_n_cusp_charRestrict k n hn χ).maxGenEigenspace μ = ⊤ :=
  Module.End.iSup_maxGenEigenspace_eq_top
    (heckeT_n_cusp_charRestrict k n hn χ)

/-! ### Simultaneous eigenform basis: proof infrastructure

The cusp form character space `S_k(Gamma_1(N), chi)` has a basis of
simultaneous Hecke eigenforms, orthogonal w.r.t. the level-N Petersson product.

**Proof strategy** (following [DS] Theorem 5.5.4, [Miy] Theorem 4.5.5):

Step 1 (Joint eigenspace decomposition):
  The family `{T_n : (n, N) = 1}` of Hecke operators restricted to `cuspFormCharSpace k chi`
  is pairwise commutative (`heckeT_n_cusp_charRestrict_commute`) and individually
  triangularizable (`heckeFamily_triangularizable`). By Mathlib's
  `iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`,
  the joint generalized eigenspaces span the whole space.

Step 2 (Basis extraction):
  Pick a basis from each non-zero joint eigenspace. Each basis vector is a
  simultaneous eigenform (`IsCommonEigenfunctionCusp`).

Step 3 (Orthogonality):
  For distinct eigenforms from different joint eigenspaces, use
  `heckeT_n_adjoint_on_charSpace` to show `petN f g = 0`.
  Within each eigenspace, apply Gram-Schmidt using `petN_innerProductCore`. -/

private lemma heckeT_n_cusp_charRestrict_commute
    (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    Commute (heckeT_n_cusp_charRestrict k m hm χ) (heckeT_n_cusp_charRestrict k n hn χ) := by
  show heckeT_n_cusp_charRestrict k m hm χ * heckeT_n_cusp_charRestrict k n hn χ =
    heckeT_n_cusp_charRestrict k n hn χ * heckeT_n_cusp_charRestrict k m hm χ
  apply LinearMap.ext
  intro ⟨f, hf⟩
  simp only [Module.End.mul_apply]
  exact Subtype.ext (heckeT_n_cusp_comm m n f)

private abbrev CoprimeIndex (N : ℕ) := { n : ℕ+ // Nat.Coprime n.val N }

private noncomputable def heckeFamily (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ) :
    CoprimeIndex N → Module.End ℂ (cuspFormCharSpace k chi) :=
  fun ⟨n, hn⟩ ↦ haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n_cusp_charRestrict k n.val hn chi

private lemma heckeFamily_pairwise_commute (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ) :
    Pairwise fun i j ↦ Commute (heckeFamily k chi i) (heckeFamily k chi j) := by
  intro ⟨m, hm⟩ ⟨n, hn⟩ _hmn
  haveI : NeZero m.val := ⟨m.pos.ne'⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  exact heckeT_n_cusp_charRestrict_commute chi m.val n.val hm hn

private lemma heckeFamily_triangularizable (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k chi)]
    (i : CoprimeIndex N) :
    ⨆ μ : ℂ, Module.End.maxGenEigenspace (heckeFamily k chi i) μ = ⊤ := by
  obtain ⟨⟨n, hn_pos⟩, hn⟩ := i
  haveI : NeZero n := ⟨hn_pos.ne'⟩
  exact Module.End.iSup_maxGenEigenspace_eq_top _

private lemma heckeFamily_joint_eigenspace_top (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k chi)] :
    ⨆ ev : CoprimeIndex N → ℂ,
      ⨅ i, Module.End.maxGenEigenspace (heckeFamily k chi i) (ev i) = ⊤ :=
  Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (heckeFamily k chi) (heckeFamily_pairwise_commute k chi)
    (heckeFamily_triangularizable k chi)

private lemma heckeFamily_isFinitelySemisimple (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k chi)]
    (i : CoprimeIndex N) :
    (heckeFamily k chi i).IsFinitelySemisimple := by
  obtain ⟨⟨n, hn_pos⟩, hn⟩ := i
  haveI : NeZero n := ⟨hn_pos.ne'⟩
  set T := heckeT_n_cusp_charRestrict k n hn chi
  letI ipCore : InnerProductSpace.Core ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    petN_innerProductCore
  letI : NormedAddCommGroup (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ ipCore
  letI : InnerProductSpace ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    InnerProductSpace.ofCore (𝕜 := ℂ) (F := CuspForm ((Gamma1 N).map (mapGL ℝ)) k) inferInstance
  set χn_inv : ℂ := ↑(chi (ZMod.unitOfCoprime n hn))⁻¹
  obtain ⟨c, hc_sq⟩ := IsAlgClosed.exists_pow_nat_eq χn_inv (show 0 < 2 from two_pos)
  have hχn_inv_ne : χn_inv ≠ 0 := by
    simp only [χn_inv]; exact_mod_cast Units.ne_zero ((chi (ZMod.unitOfCoprime n hn))⁻¹ : ℂˣ)
  have hc_ne : c ≠ 0 := by
    intro hc; rw [hc, zero_pow (by norm_num : 2 ≠ 0)] at hc_sq; exact hχn_inv_ne hc_sq.symm
  have h_norm_χn_inv : ‖χn_inv‖ = 1 := by
    have h_fin : IsOfFinOrder ((chi (ZMod.unitOfCoprime n hn))⁻¹ : ℂˣ) :=
      (MonoidHom.isOfFinOrder chi (isOfFinOrder_of_finite (ZMod.unitOfCoprime n hn))).inv
    exact ((Units.coeHom ℂ).isOfFinOrder h_fin).norm_eq_one
  have h_conj_mul_c : starRingEnd ℂ c * c = 1 := by
    have h_norm_c_sq : ‖c‖ ^ 2 = 1 := by
      have : ‖c ^ 2‖ = 1 := by rw [hc_sq]; exact h_norm_χn_inv
      rwa [norm_pow] at this
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h_norm_c_sq,
      Complex.ofReal_one]
  have h_symm : LinearMap.IsSymmetric (c • T) := by
    intro x y
    change (ipCore.inner ((c • T) x).val y.val : ℂ) = ipCore.inner x.val ((c • T) y).val
    have hval_x : ((c • T) x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        c • heckeT_n_cusp k n x.val := rfl
    have hval_y : ((c • T) y : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        c • heckeT_n_cusp k n y.val := rfl
    rw [hval_x, hval_y]
    show petN (c • heckeT_n_cusp k n x.val) y.val = petN x.val (c • heckeT_n_cusp k n y.val)
    rw [petN_conj_smul_left' c (heckeT_n_cusp k n x.val) y.val]
    rw [heckeT_n_adjoint_on_charSpace chi n hn x.prop y.prop]
    rw [petN_smul_right c x.val (heckeT_n_cusp k n y.val)]
    show starRingEnd ℂ c * (χn_inv * _) = c * _
    rw [← hc_sq, sq]
    have h_key : ∀ (P : ℂ), starRingEnd ℂ c * (c * c * P) = c * P := by
      intro P
      have : starRingEnd ℂ c * (c * c * P) = (starRingEnd ℂ c * c) * (c * P) := by ring
      rw [this, h_conj_mul_c, one_mul]
    exact h_key _
  rw [Module.End.isFinitelySemisimple_iff_isSemisimple]
  have h_semi_cT : (c • T).IsSemisimple := by
    rw [← Module.End.isFinitelySemisimple_iff_isSemisimple]
    exact h_symm.isFinitelySemisimple
  exact (Module.End.IsSemisimple_smul_iff hc_ne).mp h_semi_cT

private lemma joint_eigenspace_mem_isCommonEigenfunction
    (chi : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k chi)]
    (ev : CoprimeIndex N → ℂ)
    {f : cuspFormCharSpace k chi}
    (hf : f ∈ ⨅ i, Module.End.maxGenEigenspace (heckeFamily k chi i) (ev i))
    (hf_ne : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ≠ 0) :
    IsCommonEigenfunctionCusp k (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  intro n hn_cop
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  let i₀ : CoprimeIndex N := ⟨n, hn_cop⟩
  have hf_i : f ∈ Module.End.maxGenEigenspace (heckeFamily k chi i₀) (ev i₀) :=
    iInf_le (fun i ↦ Module.End.maxGenEigenspace (heckeFamily k chi i) (ev i)) i₀ hf
  have h_ss := heckeFamily_isFinitelySemisimple k chi i₀
  rw [Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace h_ss] at hf_i
  have h_eig := Module.End.mem_eigenspace_iff.mp hf_i
  have h_cusp : heckeT_n_cusp k n.val (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ev i₀ • (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    have h_eq := congr_arg Subtype.val h_eig
    exact h_eq
  exact ⟨ev i₀, h_cusp⟩

private lemma eigenforms_orthogonal_of_distinct_eigenvalues
    (chi : (ZMod N)ˣ →* ℂˣ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_char : f ∈ cuspFormCharSpace k chi) (hg_char : g ∈ cuspFormCharSpace k chi)
    {n : ℕ} [NeZero n] (hn : Nat.Coprime n N)
    (a_f b_g : ℂ)
    (hf_eig : heckeT_n_cusp k n f = a_f • f)
    (hg_eig : heckeT_n_cusp k n g = b_g • g)
    (h_diff : starRingEnd ℂ a_f ≠ (↑(chi (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * b_g) :
    petN f g = 0 := by
  have h_adj := heckeT_n_adjoint_on_charSpace chi n hn hf_char hg_char
  rw [hf_eig] at h_adj
  rw [petN_conj_smul_left'] at h_adj
  rw [hg_eig, petN_smul_right] at h_adj
  rw [← mul_assoc] at h_adj
  have h_eq : (starRingEnd ℂ a_f - (↑(chi (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * b_g) *
      petN f g = 0 := by
    rw [sub_mul, h_adj, sub_self]
  exact (mul_eq_zero.mp h_eq).resolve_left (sub_ne_zero.mpr h_diff)

private lemma heckeFamily_commute_all (χ : (ZMod N)ˣ →* ℂˣ) (i j : CoprimeIndex N) :
    Commute (heckeFamily k χ i) (heckeFamily k χ j) := by
  by_cases hij : i = j
  · subst hij; exact Commute.refl _
  · exact heckeFamily_pairwise_commute k χ hij

private lemma heckeFamily_mapsTo_maxGenEigenspace (χ : (ZMod N)ˣ →* ℂˣ) :
    ∀ i j : CoprimeIndex N, ∀ φ : ℂ,
      Set.MapsTo (heckeFamily k χ i)
        ((heckeFamily k χ j).maxGenEigenspace φ)
        ((heckeFamily k χ j).maxGenEigenspace φ) := fun i j φ ↦ Module.End.mapsTo_maxGenEigenspace_of_comm (heckeFamily_commute_all χ j i) φ

private lemma heckeFamily_iSupIndep_iInf_maxGenEigenspace
    (χ : (ZMod N)ˣ →* ℂˣ) :
    iSupIndep (fun ev : CoprimeIndex N → ℂ ↦ ⨅ i, (heckeFamily k χ i).maxGenEigenspace (ev i)) :=
  Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (heckeFamily k χ) (heckeFamily_mapsTo_maxGenEigenspace χ)

private lemma heckeFamily_iInf_eq (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)]
    (ev : CoprimeIndex N → ℂ) :
    (⨅ i, (heckeFamily k χ i).maxGenEigenspace (ev i)) =
      ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i) := by
  refine iInf_congr (fun i ↦ ?_)
  exact Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
    (heckeFamily_isFinitelySemisimple k χ i) (ev i)

private lemma heckeFamily_iSupIndep_iInf_eigenspace
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] :
    iSupIndep (fun ev : CoprimeIndex N → ℂ ↦ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i)) := by
  have h := heckeFamily_iSupIndep_iInf_maxGenEigenspace (k := k) χ
  refine h.mono fun ev ↦ ?_
  rw [heckeFamily_iInf_eq]

private lemma heckeFamily_iSup_iInf_eigenspace_eq_top
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] :
    ⨆ ev : CoprimeIndex N → ℂ,
      ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i) = ⊤ := by
  rw [← heckeFamily_joint_eigenspace_top k χ]
  exact iSup_congr (fun ev ↦ (heckeFamily_iInf_eq χ ev).symm)

open Classical in
private lemma heckeFamily_directSum_isInternal
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] :
    DirectSum.IsInternal (fun ev : CoprimeIndex N → ℂ ↦ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i)) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (heckeFamily_iSupIndep_iInf_eigenspace χ)
    (heckeFamily_iSup_iInf_eigenspace_eq_top χ)

private lemma heckeT_n_eigenvalue_chi_hecke
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) (hf_ne : f ≠ 0)
    {n : ℕ} [NeZero n] (hn : Nat.Coprime n N) {a : ℂ}
    (hf_eig : heckeT_n_cusp k n f = a • f) :
    starRingEnd ℂ a = (↑(χ (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * a := by
  have h_adj := heckeT_n_adjoint_on_charSpace χ n hn hf hf
  rw [hf_eig] at h_adj
  rw [petN_conj_smul_left', petN_smul_right] at h_adj
  rw [← mul_assoc] at h_adj
  have hpos : petN f f ≠ 0 := fun hpet ↦ hf_ne (petN_definite f hpet)
  exact mul_right_cancel₀ hpos h_adj

private lemma eigenforms_orthogonal_of_ne_eigenvalues
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf_char : f ∈ cuspFormCharSpace k χ) (hg_char : g ∈ cuspFormCharSpace k χ)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    {n : ℕ} [NeZero n] (hn : Nat.Coprime n N) {a b : ℂ}
    (hf_eig : heckeT_n_cusp k n f = a • f)
    (hg_eig : heckeT_n_cusp k n g = b • g)
    (h_diff_ab : a ≠ b) :
    petN f g = 0 := by
  refine eigenforms_orthogonal_of_distinct_eigenvalues χ f g hf_char hg_char hn
    a b hf_eig hg_eig ?_
  intro h_eq
  have h_chi_f : starRingEnd ℂ a = (↑(χ (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * a :=
    heckeT_n_eigenvalue_chi_hecke χ hf_char hf_ne hn hf_eig
  rw [h_chi_f] at h_eq
  have hχ_ne : (↑(χ (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero ((χ (ZMod.unitOfCoprime n hn))⁻¹ : ℂˣ)
  exact h_diff_ab (mul_left_cancel₀ hχ_ne h_eq)

private lemma joint_eigenspace_orthogonal
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)]
    {ev₁ ev₂ : CoprimeIndex N → ℂ} (h_ne : ev₁ ≠ ev₂)
    {f g : cuspFormCharSpace k χ}
    (hf : f ∈ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev₁ i))
    (hg : g ∈ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev₂ i))
    (hf_ne : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ≠ 0)
    (hg_ne : (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ≠ 0) :
    petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 := by
  obtain ⟨n_idx, hn_diff⟩ := Function.ne_iff.mp h_ne
  obtain ⟨n_pn, hn_cop⟩ := n_idx
  haveI : NeZero n_pn.val := ⟨n_pn.pos.ne'⟩
  have hf_mem : f ∈ Module.End.eigenspace (heckeFamily k χ ⟨n_pn, hn_cop⟩) (ev₁ ⟨n_pn, hn_cop⟩) :=
    (Submodule.mem_iInf _).mp hf _
  have hg_mem : g ∈ Module.End.eigenspace (heckeFamily k χ ⟨n_pn, hn_cop⟩) (ev₂ ⟨n_pn, hn_cop⟩) :=
    (Submodule.mem_iInf _).mp hg _
  have hf_eq_sub : heckeFamily k χ ⟨n_pn, hn_cop⟩ f = ev₁ ⟨n_pn, hn_cop⟩ • f :=
    Module.End.mem_eigenspace_iff.mp hf_mem
  have hg_eq_sub : heckeFamily k χ ⟨n_pn, hn_cop⟩ g = ev₂ ⟨n_pn, hn_cop⟩ • g :=
    Module.End.mem_eigenspace_iff.mp hg_mem
  have hf_eq : heckeT_n_cusp k n_pn.val (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ev₁ ⟨n_pn, hn_cop⟩ • (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    have := congr_arg Subtype.val hf_eq_sub
    exact this
  have hg_eq : heckeT_n_cusp k n_pn.val (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ev₂ ⟨n_pn, hn_cop⟩ • (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    have := congr_arg Subtype.val hg_eq_sub
    exact this
  exact eigenforms_orthogonal_of_ne_eigenvalues χ f.prop g.prop hf_ne hg_ne hn_cop
    hf_eq hg_eq hn_diff

private lemma joint_eigenspace_subset_isCommonEigenfunction
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)]
    (ev : CoprimeIndex N → ℂ)
    {f : cuspFormCharSpace k χ}
    (hf : f ∈ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i)) :
    ∀ n : ℕ+, Nat.Coprime n.val N →
      haveI : NeZero n.val := ⟨n.pos.ne'⟩
      ∃ a : ℂ, heckeT_n_cusp k n.val (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        a • (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  intro n hn_cop
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  refine ⟨ev ⟨n, hn_cop⟩, ?_⟩
  have hf_mem : f ∈ Module.End.eigenspace (heckeFamily k χ ⟨n, hn_cop⟩) (ev ⟨n, hn_cop⟩) :=
    (Submodule.mem_iInf _).mp hf _
  have h_eq := Module.End.mem_eigenspace_iff.mp hf_mem
  exact congr_arg Subtype.val h_eq

theorem exists_simultaneous_eigenform_basis
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] :
    ∃ (B : Finset (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)),
      (∀ f ∈ B, f ∈ cuspFormCharSpace k χ) ∧
      (∀ f ∈ B, IsCommonEigenfunctionCusp k f) ∧
      (∀ f g, f ∈ B → g ∈ B → f ≠ g → petN f g = 0) := by
  classical
  letI ipCore : InnerProductSpace.Core ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    petN_innerProductCore
  letI : NormedAddCommGroup (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ ipCore
  letI : InnerProductSpace ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    InnerProductSpace.ofCore (𝕜 := ℂ)
      (F := CuspForm ((Gamma1 N).map (mapGL ℝ)) k) inferInstance
  have h_internal := heckeFamily_directSum_isInternal (k := k) χ
  let W : (CoprimeIndex N → ℂ) → Submodule ℂ (cuspFormCharSpace k χ) :=
    fun ev ↦ ⨅ i, Module.End.eigenspace (heckeFamily k χ i) (ev i)
  let evToBasis : (CoprimeIndex N → ℂ) → Type := fun ev ↦ Fin (Module.finrank ℂ (W ev))
  let basisAtEv : ∀ ev, Module.Basis (evToBasis ev) ℂ (W ev) :=
    fun ev ↦ (stdOrthonormalBasis ℂ (W ev)).toBasis
  let onbAtEv : ∀ ev, OrthonormalBasis (evToBasis ev) ℂ (W ev) :=
    fun ev ↦ stdOrthonormalBasis ℂ (W ev)
  let bigBasis : Module.Basis (Σ ev, evToBasis ev) ℂ (cuspFormCharSpace k χ) :=
    h_internal.collectedBasis basisAtEv
  have h_finite : Finite (Σ ev, evToBasis ev) := Module.Finite.finite_basis bigBasis
  haveI : Fintype (Σ ev, evToBasis ev) := Fintype.ofFinite _
  refine ⟨(Finset.univ : Finset (Σ ev, evToBasis ev)).image
    (fun x ↦ ((bigBasis x : cuspFormCharSpace k χ) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k)), ?_, ?_, ?_⟩
  · intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨x, _, rfl⟩ := hf
    exact (bigBasis x).property
  · intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨x, _, rfl⟩ := hf
    have hmem : (bigBasis x : cuspFormCharSpace k χ) ∈ W x.1 :=
      h_internal.collectedBasis_mem basisAtEv x
    intro n hn_cop
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    exact joint_eigenspace_subset_isCommonEigenfunction χ x.1 hmem n hn_cop
  · intro f g hf hg hfg
    rw [Finset.mem_image] at hf hg
    obtain ⟨x, _, hx⟩ := hf
    obtain ⟨y, _, hy⟩ := hg
    subst hx hy
    by_cases hxy_fst : x.1 = y.1
    · obtain ⟨ev_x, ix⟩ := x
      obtain ⟨ev_y, iy⟩ := y
      simp only at hxy_fst
      subst hxy_fst
      have hi_ne : ix ≠ iy := fun h ↦ hfg (by subst h; rfl)
      have h_basis_eq_onb : ∀ (j : Fin (Module.finrank ℂ (W ev_x))),
          (basisAtEv ev_x j : W ev_x) = onbAtEv ev_x j := by
        intro j
        show ((stdOrthonormalBasis ℂ (W ev_x)).toBasis j : W ev_x) =
          stdOrthonormalBasis ℂ (W ev_x) j
        exact OrthonormalBasis.coe_toBasis (stdOrthonormalBasis ℂ (W ev_x)) ▸ rfl
      have h_inner_W : @inner ℂ (W ev_x) _ (onbAtEv ev_x ix) (onbAtEv ev_x iy) = 0 :=
        (onbAtEv ev_x).orthonormal.2 hi_ne
      have h_inner_eq : @inner ℂ (W ev_x) _ (basisAtEv ev_x ix) (basisAtEv ev_x iy) =
          @inner ℂ (W ev_x) _ (onbAtEv ev_x ix) (onbAtEv ev_x iy) := by
        simp_rw [h_basis_eq_onb]
      have h_inner_zero : @inner ℂ (W ev_x) _ (basisAtEv ev_x ix) (basisAtEv ev_x iy) = 0 := by
        rw [h_inner_eq, h_inner_W]
      have h_collect_x :
          (bigBasis ⟨ev_x, ix⟩ : cuspFormCharSpace k χ) =
            ((basisAtEv ev_x ix : W ev_x) : cuspFormCharSpace k χ) := by
        show (h_internal.collectedBasis basisAtEv ⟨ev_x, ix⟩ : cuspFormCharSpace k χ) = _
        rw [h_internal.collectedBasis_coe basisAtEv]
      have h_collect_y :
          (bigBasis ⟨ev_x, iy⟩ : cuspFormCharSpace k χ) =
            ((basisAtEv ev_x iy : W ev_x) : cuspFormCharSpace k χ) := by
        show (h_internal.collectedBasis basisAtEv ⟨ev_x, iy⟩ : cuspFormCharSpace k χ) = _
        rw [h_internal.collectedBasis_coe basisAtEv]
      have h_pet_eq : petN
          ((bigBasis ⟨ev_x, ix⟩ : cuspFormCharSpace k χ) :
            CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          ((bigBasis ⟨ev_x, iy⟩ : cuspFormCharSpace k χ) :
            CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
          @inner ℂ (cuspFormCharSpace k χ) _
            (bigBasis ⟨ev_x, ix⟩) (bigBasis ⟨ev_x, iy⟩) := rfl
      have h_inner_lift :
          @inner ℂ (cuspFormCharSpace k χ) _
            (bigBasis ⟨ev_x, ix⟩) (bigBasis ⟨ev_x, iy⟩) =
          @inner ℂ (W ev_x) _ (basisAtEv ev_x ix) (basisAtEv ev_x iy) := by
        rw [h_collect_x, h_collect_y]
        rfl
      rw [h_pet_eq, h_inner_lift, h_inner_zero]
    · have hx_mem : (bigBasis x : cuspFormCharSpace k χ) ∈ W x.1 :=
        h_internal.collectedBasis_mem basisAtEv x
      have hy_mem : (bigBasis y : cuspFormCharSpace k χ) ∈ W y.1 :=
        h_internal.collectedBasis_mem basisAtEv y
      have hbb_x_ne : (bigBasis x : cuspFormCharSpace k χ) ≠ 0 := bigBasis.ne_zero x
      have hbb_y_ne : (bigBasis y : cuspFormCharSpace k χ) ≠ 0 := bigBasis.ne_zero y
      have hx_ne : ((bigBasis x : cuspFormCharSpace k χ) :
          CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ≠ 0 := by
        intro h
        apply hbb_x_ne
        exact Subtype.ext h
      have hy_ne : ((bigBasis y : cuspFormCharSpace k χ) :
          CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ≠ 0 := by
        intro h
        apply hbb_y_ne
        exact Subtype.ext h
      exact joint_eigenspace_orthogonal χ hxy_fst hx_mem hy_mem hx_ne hy_ne

end HeckeRing.GL2
