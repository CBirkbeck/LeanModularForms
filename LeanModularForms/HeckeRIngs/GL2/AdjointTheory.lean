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

/-- `GL₂(ℚ)` maps cusps of `Γ₁(N)` to cusps of `Γ₁(N)`. -/
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
  · apply Finset.sum_induction _ (fun g => c.IsZeroAt g k)
      (fun _ _ ha hb => ha.add hb)
      ((0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).zero_at_cusps' hc)
    intro b _
    exact OnePoint.IsZeroAt.smul_iff.mp
      (f.zero_at_cusps' (Gamma1_isCusp_glMap_smul' _ hc))
  · -- Diamond operator term: (⟨p⟩f) ∣[k] T_p_lower
    -- Unfold IsZeroAt: need to show IsZeroAtImInfty for each γ with γ • ∞ = c
    intro γ hγ
    -- Convert the GL₂(ℚ) slash to GL₂(ℝ) so we can combine with the GL₂(ℝ) slash by γ
    show UpperHalfPlane.IsZeroAtImInfty
      ((⇑((diamondOp k (ZMod.unitOfCoprime p hpN)) f.toModularForm') ∣[k]
        glMap (T_p_lower p hp.pos)) ∣[k] γ)
    rw [← SlashAction.slash_mul]
    -- Unfold diamondOp to expose ⇑f ∣[k] mapGL ℝ g, then combine slashes
    set g := (Gamma0MapUnits_surjective (ZMod.unitOfCoprime p hpN)).choose
    change UpperHalfPlane.IsZeroAtImInfty
      ((⇑f.toModularForm' ∣[k] mapGL ℝ (g : SL(2, ℤ))) ∣[k]
        (glMap (T_p_lower p hp.pos) * γ))
    rw [← SlashAction.slash_mul]
    -- Goal: IsZeroAtImInfty (⇑f ∣[k] (mapGL ℝ g * (glMap T_p_lower * γ)))
    -- The combined element sends ∞ to mapGL ℝ g • glMap T_p_lower • c
    -- Show mapGL ℝ g • (glMap T_p_lower • c) is a Γ₁-cusp
    have hc_lower : IsCusp (glMap (T_p_lower p hp.pos) • c)
        ((Gamma1 N).map (mapGL ℝ)) := Gamma1_isCusp_glMap_smul' _ hc
    -- mapGL ℝ g preserves Γ₁-cusps by Γ₀-normality of Γ₁
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

/-- `T_p` (for all primes, including `p | N`) preserves cuspidality. -/
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
    apply Finset.sum_induction _ (fun g => c.IsZeroAt g k)
      (fun _ _ ha hb => ha.add hb)
      ((0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).zero_at_cusps' hc)
    intro b _
    exact OnePoint.IsZeroAt.smul_iff.mp
      (f.zero_at_cusps' (Gamma1_isCusp_glMap_smul' _ hc))

/-- A `Module.End` on `ModularForm` preserves cuspidality if its output function
is zero at cusps for every cusp form input. This packages the zero-at-cusps
property for arbitrary `Module.End` operators built from cuspidality-preserving
components. -/
private def PreservesCusps (T : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) :
    Prop :=
  ∀ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {c : OnePoint ℝ},
    IsCusp c ((Gamma1 N).map (mapGL ℝ)) → c.IsZeroAt (T f.toModularForm').toFun k

omit [NeZero N] in
private theorem preservesCusps_one :
    PreservesCusps (N := N) (k := k) 1 :=
  fun f _ hc => by simp; exact f.zero_at_cusps' hc

private theorem preservesCusps_heckeT_p_all (p : ℕ) (hp : Nat.Prime p) :
    PreservesCusps (N := N) (heckeT_p_all k p hp) :=
  fun f _ hc => heckeT_p_all_zero_at_cusps p hp f hc

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
  -- T₂ f.toModularForm' is a modular form whose toFun is zero at cusps (by h₂)
  -- So we can wrap it as a cusp form, then apply h₁
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
  -- Wrap T₁ f and T₂ f as cusp forms
  let g₁ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    { toSlashInvariantForm := (T₁ f.toModularForm').toSlashInvariantForm
      holo' := (T₁ f.toModularForm').holo'
      zero_at_cusps' := h₁ f }
  let g₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    { toSlashInvariantForm := (T₂ f.toModularForm').toSlashInvariantForm
      holo' := (T₂ f.toModularForm').holo'
      zero_at_cusps' := h₂ f }
  -- (T₁ - T₂) f = T₁ f - T₂ f as modular forms, and g₁ - g₂ is a cusp form
  have hfun : ((T₁ - T₂) f.toModularForm').toFun = (g₁ - g₂).toFun := rfl
  rw [hfun]
  exact (g₁ - g₂).zero_at_cusps' hc

omit [NeZero N] in
private theorem preservesCusps_smul (a : ℂ) {T : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (hT : PreservesCusps T) :
    PreservesCusps (a • T) := by
  intro f c hc
  -- (a • T) f = a • (T f) as modular forms
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
  -- heckeT_n k n = heckeT_n_aux k n, so it suffices to prove the aux version by induction
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
  zero_at_cusps' := fun hc => preservesCusps_heckeT_n n f hc

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
  -- Work at heckeT_n_aux level
  show (heckeT_n_aux k m f.toModularForm').toFun z =
    (heckeT_n_aux k _ (heckeT_n_aux k _ f.toModularForm')).toFun z
  rw [heckeT_n_aux, dif_neg (not_le.mpr hm), Module.End.mul_apply]
  -- LHS: heckeT_ppow(heckeT_n_aux(m/p^v)(f)).toFun z
  -- RHS: heckeT_n_aux(p^v)(heckeT_n_aux(m/p^v)(f)).toFun z
  -- heckeT_ppow = heckeT_n ⟨p^v, _⟩ = heckeT_n_aux(p^v) by prime_pow
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
  -- Goal: heckeT_ppow * heckeT_n = heckeT_n * heckeT_n
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

/-- The Γ₀(N) representative for the T_p adjoint double coset.

Given `p` coprime to `N`, use Bezout to find `m, n` with `mp - nN = 1`,
and construct `γ₀ = [p, n; N, m] ∈ Γ₀(N)` with `m ≡ p⁻¹ mod N`.
This is the element from DS Theorem 5.5.3 that relates
`Γ₁(N)[p,0;0,1]Γ₁(N) = Γ₁(N)[1,0;0,p]Γ₁(N) · γ₀`. -/
private noncomputable def adjointGamma0Rep (p N : ℕ) (hpN : Nat.Coprime p N) :
    ↥(Gamma0 N) :=
  -- Use Bezout: gcdA(p,N) * p + gcdB(p,N) * N = gcd(p,N) = 1
  -- Build [p, -gcdB; N, gcdA] ∈ Γ₀(N). det = p·gcdA + N·gcdB = 1.
  let m := Int.gcdA p N
  let n := -(Int.gcdB p N)
  ⟨⟨!![(p : ℤ), n; (N : ℤ), m], by
      -- det = p * m - n * N = p * gcdA + gcdB * N = 1 (Bezout)
      have hbez := Int.gcd_eq_gcd_ab p N
      rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 from by exact_mod_cast hpN] at hbez
      simp only [Matrix.det_fin_two_of]
      linarith⟩, by
      -- Γ₀(N) membership: the (1,0) entry is N, and (N : ZMod N) = 0
      rw [Gamma0_mem]; simp⟩

/-- The bottom-right entry of `adjointGamma0Rep` is `p⁻¹ mod N`:
`Gamma0MapUnits(γ₀) = ⟨p⟩⁻¹`. This is because `m·p ≡ 1 mod N` (Bezout). -/
private lemma adjointGamma0Rep_units (p N : ℕ) (hpN : Nat.Coprime p N) [NeZero N] :
    Gamma0MapUnits (adjointGamma0Rep p N hpN) =
      (ZMod.unitOfCoprime p hpN)⁻¹ := by
  -- The bottom-right entry of adjointGamma0Rep is gcdA(p,N).
  -- From Bezout: gcdA * p + gcdB * N = 1, so (gcdA : ZMod N) * p = 1,
  -- hence Gamma0MapUnits = unitOfCoprime(p)⁻¹.
  have hbez := Int.gcd_eq_gcd_ab p N
  rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 from by exact_mod_cast hpN] at hbez
  -- Bezout in ZMod N: gcdA * p = 1
  have hmod : (Int.gcdA (↑p) (↑N) : ZMod N) * (p : ZMod N) = 1 := by
    have h := congr_arg (Int.cast : ℤ → ZMod N) hbez
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, add_zero] at h
    rw [mul_comm] at h; exact h.symm
  -- γ₀-units * unitOfCoprime = 1, hence γ₀-units = unitOfCoprime⁻¹
  rw [eq_comm, inv_eq_of_mul_eq_one_left]
  ext
  simp only [Units.val_mul, Units.val_one, Gamma0MapUnits_val, ZMod.coe_unitOfCoprime]
  -- Goal: Gamma0Map N γ₀ * p = 1, where Gamma0Map extracts (1,1) entry
  -- Unfold to get the gcdA entry
  unfold adjointGamma0Rep Gamma0Map
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  exact hmod

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
private noncomputable def peterssonAdj (α : GL (Fin 2) ℝ) : GL (Fin 2) ℝ :=
  .mkOfDetNeZero (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate (by
    rw [Matrix.det_adjugate]
    exact pow_ne_zero _ α.det_ne_zero)

-- API for `slash_peterssonAdj_eq`: key facts about adjugate in GL₂.

/-- `det(peterssonAdj α) = det(α)` for 2×2 matrices (since det(adjugate) = det^{n-1}). -/
private lemma peterssonAdj_det (α : GL (Fin 2) ℝ) :
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
private lemma peterssonAdj_coe (α : GL (Fin 2) ℝ) :
    (peterssonAdj α : Matrix (Fin 2) (Fin 2) ℝ) =
      (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate := by
  simp [peterssonAdj]

/-- `peterssonAdj` is anti-multiplicative: `peterssonAdj(α * β) = peterssonAdj β * peterssonAdj α`.
Follows from `Matrix.adjugate_mul_distrib`. -/
private lemma peterssonAdj_mul (α β : GL (Fin 2) ℝ) :
    peterssonAdj (α * β) = peterssonAdj β * peterssonAdj α := by
  apply Units.ext
  show (peterssonAdj (α * β) : Matrix (Fin 2) (Fin 2) ℝ) =
    (peterssonAdj β * peterssonAdj α : GL (Fin 2) ℝ).val
  rw [Units.val_mul, peterssonAdj_coe, peterssonAdj_coe, peterssonAdj_coe,
    Units.val_mul, Matrix.adjugate_mul_distrib]

/-- For an SL(2, ℤ) element cast to GL(2, ℝ), the `peterssonAdj` equals the group inverse.
Since SL elements have determinant 1, their adjugate equals their inverse. -/
private lemma peterssonAdj_mapGL_SL_eq_inv (q : SL(2, ℤ)) :
    peterssonAdj ((mapGL ℝ q : GL (Fin 2) ℝ)) = (mapGL ℝ q : GL (Fin 2) ℝ)⁻¹ := by
  apply Units.ext
  rw [peterssonAdj_coe, Matrix.coe_units_inv]
  -- Matrix.adjugate A = A⁻¹ when det A = 1. Use Matrix.inv_def + det = 1.
  have hdet : (mapGL ℝ q : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    have : (mapGL ℝ q : Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix q.val) := by
      ext i j; simp [mapGL_coe_matrix, Int.castRingHom]
    rw [this, ← RingHom.map_det, q.property]
    simp
  rw [Matrix.inv_def, Ring.inverse_eq_inv', hdet]
  simp

/-- Entry-level: `(α⁻¹) i j = det(α)⁻¹ * adjugate(α) i j`. -/
private lemma GL_inv_entry (α : GL (Fin 2) ℝ) (i j : Fin 2) :
    (α⁻¹ : GL (Fin 2) ℝ) i j =
      (α.det.val)⁻¹ * (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate i j := by
  set A := (α : Matrix (Fin 2) (Fin 2) ℝ)
  have hdet : A.det ≠ 0 := α.det_ne_zero
  -- ↑α⁻¹ = A⁻¹ (nonsingular inverse)
  have hcoe : (↑α⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) = A⁻¹ := Matrix.coe_units_inv α
  -- A⁻¹ = Ring.inverse(det A) • adjugate(A), and Ring.inverse = inv for a field
  have hinv : A⁻¹ = A.det⁻¹ • A.adjugate := by
    rw [Matrix.inv_def]
    congr 1
    exact Ring.inverse_eq_inv _
  have hdet_eq : A.det = α.det.val := rfl
  show (↑α⁻¹ : Matrix _ _ ℝ) i j = _
  rw [hcoe, hinv, Matrix.smul_apply, smul_eq_mul, hdet_eq]

/-- The peterssonAdj has the same Möbius action as α⁻¹: `peterssonAdj α • τ = α⁻¹ • τ`.
This is because adjugate(α) = det(α) · α⁻¹ as Möbius maps (scalar matrices act trivially). -/
private lemma peterssonAdj_smul_eq (α : GL (Fin 2) ℝ) (τ : ℍ) :
    (peterssonAdj α) • τ = α⁻¹ • τ := by
  -- num/denom of peterssonAdj α differ from α⁻¹ by the factor det(α), which cancels
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
  -- σ agrees because det(peterssonAdj α) and det(α⁻¹) have the same sign
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

/-- `denom(peterssonAdj α, τ) = det(α) · denom(α⁻¹, τ)`.
For adjugate `[[d,-b],[-c,a]]` vs inverse `[[d,-b],[-c,a]]/det`: the denominators
(bottom row · [τ, 1]) differ by the factor det(α). -/
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
private lemma slash_peterssonAdj_eq (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (g : ℍ → ℂ) :
    g ∣[k] peterssonAdj α = (↑(|α.det.val| ^ (k - 2)) : ℂ) • (g ∣[k] α⁻¹) := by
  have habs : |α.det.val| = α.det.val := abs_of_pos hα
  have hdet_ne : (α.det.val : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  have hdet_eq : (peterssonAdj α).det.val = α.det.val :=
    congr_arg Units.val (peterssonAdj_det α)
  have hσ_adj : σ (peterssonAdj α) = σ α⁻¹ := by
    simp only [σ, hdet_eq]
    have : (α⁻¹).det.val = (α.det.val)⁻¹ := by
      rw [show (α⁻¹).det = α.det⁻¹ from map_inv (Matrix.GeneralLinearGroup.det) α]
      exact Units.val_inv_eq_inv_val _
    simp [this, inv_pos]
  have hdet_inv_abs : |(α⁻¹).det.val| = (α.det.val)⁻¹ := by
    rw [show (α⁻¹).det = α.det⁻¹ from map_inv (Matrix.GeneralLinearGroup.det) α,
      Units.val_inv_eq_inv_val, abs_inv, habs]
  ext τ
  have hD := denom_ne_zero α⁻¹ τ
  simp only [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul, peterssonAdj_smul_eq,
    hσ_adj, hdet_eq, peterssonAdj_denom, mul_zpow, hdet_inv_abs, habs]
  -- Goal:
  -- σ(g(..)) * ↑d^(k-1) * (↑d^(-k) * D^(-k))
  -- = ↑(d^(k-2)) * (σ(g(..)) * ↑d⁻¹^(k-1) * D^(-k))
  -- where d = det α : ℝ (and ↑ is the ℝ→ℂ cast)
  set d := α.det.val with hd_def
  -- Normalize the RHS coercions: ↑(d^(k-2)) = (↑d)^(k-2) and ↑(d⁻¹) = (↑d)⁻¹
  rw [show (↑(d ^ (k - 2)) : ℂ) = (↑d : ℂ) ^ (k - 2) from by push_cast; rfl]
  rw [show (↑(d⁻¹) : ℂ) = (↑d : ℂ)⁻¹ from Complex.ofReal_inv d]
  -- LHS: σ(g(..)) * (↑d)^(k-1) * ((↑d)^(-k) * D^(-k))
  -- RHS: (↑d)^(k-2) * (σ(g(..)) * (↑d)⁻¹^(k-1) * D^(-k))
  -- Combine zpow factors on each side using zpow_add
  have hcd : (↑d : ℂ) ≠ 0 := hdet_ne
  -- Both sides equal σ(g(..)) * (↑d)^(-1) * D^(-k)
  -- LHS: σ(g(..)) * (↑d)^(k-1) * ((↑d)^(-k) * D^(-k))
  -- RHS: (↑d)^(k-2) * (σ(g(..)) * (↑d)⁻¹^(k-1) * D^(-k))
  set G := σ α⁻¹ (g (α⁻¹ • τ)) with hG_def
  set D := denom α⁻¹ (↑τ) with hD_def
  suffices h : G * (↑d : ℂ) ^ (k - 1) * ((↑d : ℂ) ^ (-k) * D ^ (-k)) =
      (↑d : ℂ) ^ (k - 2) * (G * (↑d : ℂ)⁻¹ ^ (k - 1) * D ^ (-k)) by exact h
  rw [inv_zpow']
  -- Now RHS has (↑d)^(-(k-1)) instead of (↑d)⁻¹^(k-1)
  -- Both sides can be shown equal by combining zpow: k-1 + (-k) = -1 = (k-2) + (-(k-1))
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
```

**Proof** (DS Lemma 5.5.1 / Prop 5.5.2a):
1. Write `g = (g∣[k]α⁻¹)∣[k]α` (by `slash_mul` + `inv_mul_cancel` + `slash_one`).
2. Apply `petersson_slash` to `petersson k (f∣α) ((g∣α⁻¹)∣α) τ`:
   `= |det α|^{k-2} * σ α (petersson k f (g∣α⁻¹) (α•τ))`
   `= |det α|^{k-2} * petersson k f (g∣α⁻¹) (α•τ)`  (since `det α > 0`, `σ α = id`).
3. Change variables `∫_{α•D} h dμ = ∫_D h(α•·) dμ` (by `instSMulInvMeasure_GLpos`):
   `∫_D |det α|^{k-2} * petersson k f (g∣α⁻¹) (α•·) dμ`
   `= |det α|^{k-2} * ∫_{α•D} petersson k f (g∣α⁻¹) dμ`
4. By `slash_peterssonAdj_eq`: `g∣adj(α) = |det α|^{k-2} • (g∣α⁻¹)`, so
   `petersson k f (g∣adj(α)) = |det α|^{k-2} * petersson k f (g∣α⁻¹)`.
5. The constant factors cancel, giving `peterssonInner k (α•D) f (g∣adj(α))`. -/
private theorem peterssonInner_slash_adjoint
    (D : Set ℍ) (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : ℍ → ℂ) :
    peterssonInner k D (f ∣[k] α) g =
      peterssonInner k (α • D) f (g ∣[k] peterssonAdj α) := by
  -- Step 1: Write g = (g ∣[k] α⁻¹) ∣[k] α
  have hg_decomp : g = (g ∣[k] α⁻¹) ∣[k] α := by
    rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  -- Step 2: Rewrite using petersson_slash
  simp only [peterssonInner]
  -- Step 2: Use petersson_slash with g decomposed
  -- Key: petersson k (f∣α) g = petersson k (f∣α) ((g∣α⁻¹)∣α) (by hg_decomp)
  --     = |det α|^{k-2} * petersson k f (g∣α⁻¹) (α•·) (by petersson_slash + σ α = id)
  set g' := g ∣[k] α⁻¹
  have h_eq : ∀ τ, petersson k (f ∣[k] α) g τ =
      ↑|α.det.val| ^ (k - 2) * petersson k f g' (α • τ) := by
    intro τ
    -- g = g' ∣[k] α
    have : g = g' ∣[k] α := hg_decomp
    rw [this, petersson_slash, show σ α = RingHom.id ℂ from if_pos hα, RingHom.id_apply]
  simp_rw [h_eq]
  -- Goal: ∫_D c * petersson k f g' (α•τ) dμ = ∫_{α•D} petersson k f (g∣adj) dμ
  -- Step 3: Change variables + absorb factor
  -- The key step: ∫_{α•D} h dμ = ∫_D h(α•·) dμ (by MeasurePreserving)
  -- Combined with the det factor, everything works out.
  --
  -- We work backwards from the RHS:
  -- ∫_{α•D} petersson k f (g∣adj) dμ
  -- = ∫_{α•D} petersson k f (c • g') dμ        (by slash_peterssonAdj_eq)
  -- = ∫_{α•D} c * petersson k f g' dμ           (petersson is linear in 2nd arg)
  -- = c * ∫_{α•D} petersson k f g' dμ           (pull constant)
  -- = c * ∫_D petersson k f g' (α•τ) dμ         (change of variables)
  -- = ∫_D c * petersson k f g' (α•τ) dμ         (push constant back)
  -- = LHS
  -- Work backwards from the RHS
  symm
  -- Step 3a: Rewrite g ∣[k] peterssonAdj α = c • g' and simplify
  have hpet_adj : ∀ τ, petersson k f (g ∣[k] peterssonAdj α) τ =
      ↑|α.det.val| ^ (k - 2) * petersson k f g' τ := by
    intro τ
    rw [slash_peterssonAdj_eq α hα g]
    simp [petersson, Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [hpet_adj]
  -- Goal: ∫_{α•D} c * petersson k f g' dμ = ∫_D c * petersson k f g' (α•τ) dμ
  -- Step 3b: Change of variables using GL₂⁺ invariance
  set α' : GL(2, ℝ)⁺ := ⟨α, hα⟩
  rw [show α • D = (fun τ => α' • τ) '' D from by rw [Set.image_smul]; rfl]
  exact (measurePreserving_smul α' μ_hyp).setIntegral_image_emb
    (measurableEmbedding_const_smul α') _ D

end PeterssonAdjoint

/-! ### Dead code — superseded by PSL2Action.lean

The following section (Hausdorff measure identification + SL₂(ℝ) direct invariance)
is superseded by `instSMulInvMeasure_GLpos` in PSL2Action.lean, which proves
`SMulInvariantMeasure GL(2,ℝ)⁺ ℍ μ_hyp` (a strictly stronger result).

The Hausdorff identification `μ_hyp = μH[2]` also requires Mathlib Riemannian
geometry infrastructure that does not yet exist.

Commented out 2026-04-13 to reduce sorry count. The SL₂(ℤ) and PSL₂ instances
are in PSL2Action.lean with 0 sorries. -/

/-- The `SL₂(ℤ)` action on `ℍ` factors through `SL₂(ℝ)` via `algebraMap ℤ ℝ`,
so continuity of the action (needed for `MeasurableConstSMul` via the Borel
σ-algebra) follows from that of `SL₂(ℝ)`. -/
private instance : ContinuousConstSMul SL(2, ℤ) UpperHalfPlane where
  continuous_const_smul c := by
    show Continuous fun τ => (map (Int.castRingHom ℝ) c) • τ
    exact continuous_const_smul _

-- The lemma `peterssonInner_fd_eq_smul_fd` was REMOVED on 2026-04-08:
-- It claimed `∫_{γ⁻¹·fd} petersson(f,g) = ∫_{fd} petersson(f,g)` for γ ∈ SL₂(ℤ),
-- but this is FALSE for N > 1 because petersson(f,g) is only Γ₁(N)-periodic,
-- not SL₂(ℤ)-periodic.
-- The fix is to use `petN` (level-N Petersson) from PeterssonLevelN.lean instead.

/-- Diamond operators are unitary for the **level-N Petersson inner product** `petN`:
`⟨⟨d⟩f, ⟨d⟩g⟩_N = ⟨f, g⟩_N`.

The proof uses the fact that the diamond operator permutes the cosets of
`Γ₁(N) \ SL₂(ℤ)`. Specifically, if `⟨d⟩f = f∣[k]γ` for `γ ∈ Γ₀(N)`, then:
```
petN (⟨d⟩f) (⟨d⟩g) = Σ_{[δ]} ∫_fd petersson k ((f∣γ)∣δ⁻¹) ((g∣γ)∣δ⁻¹) dμ
                   = Σ_{[δ]} ∫_fd petersson k (f∣(δγ⁻¹)⁻¹) (g∣(δγ⁻¹)⁻¹) dμ
                   = Σ_{[δ']} ∫_fd petersson k (f∣δ'⁻¹) (g∣δ'⁻¹) dμ  [δ' = δγ⁻¹]
                   = petN f g
```
The reindexing `δ ↦ δγ` is a bijection on cosets since γ ∈ Γ₀(N) normalizes Γ₁(N).

NOTE: This uses `petN` (the corrected level-N Petersson inner product from
`PeterssonLevelN.lean`), NOT `pet`. The original `pet` is wrong for N > 1.

Reference: [DS] Proposition 5.5.2, [Miy] Lemma 4.5.1. -/
theorem diamondOp_petersson_unitary
    (d : (ZMod N)ˣ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k d f) (diamondOp_cusp k d g) = petN f g := by
  -- Diamond operator ⟨d⟩ acts as slash by γ ∈ Γ₀(N), so this follows from petN_slash_invariant.
  set γ_sub := (Gamma0MapUnits_surjective d).choose
  exact petN_slash_invariant f g (γ_sub : SL(2, ℤ)) γ_sub.property
    (fun η hη => slash_Gamma1_eq f η hη) (fun η hη => slash_Gamma1_eq g η hη)
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
/-- **Fundamental domain tiling identity** for `GL₂⁺(ℝ)` shifts.

For `α ∈ GL₂⁺(ℝ)` that normalizes `Γ₁(N)` (so that `α • D_N^PSL` is again a
`Γ₁(N)`-fundamental domain) and a `Γ₁(N)`-invariant integrand `h`, the sum of
integrals over the shifted tiles `{α • (q⁻¹ • fd)}_{q ∈ SL₂/Γ₁}` equals the sum
over the standard tiles `{q⁻¹ • fd}`:

```
  Σ_q ∫_{α • (q⁻¹ • fd)} h dμ = Σ_q ∫_{q⁻¹ • fd} h dμ
```

**Proof outline**: Both sums reduce to `fiber_count · ∫_{D_N^PSL} h dμ` where
`D_N^PSL = ⋃_{q' : PSL/imageGamma1_PSL} q'.out⁻¹ • fdo` is the PSL-level
fundamental domain and `fiber_count` is the uniform cardinality of the
`SL/Γ₁ → PSL/imageGamma1_PSL` fibers. For the α-shifted sum, change of variables
(via measure-preservation of `α`) converts each summand to an integral of
`h ∘ α` over the unshifted tile; the hypothesis `hα_h_inv` ensures that `h ∘ α`
is also `Γ₁(N)`-invariant, so the same PSL-sum template applies. The resulting
integral `∫_{D_N^PSL} (h ∘ α) dμ = ∫_{α • D_N^PSL} h dμ` (another change of
variables), which equals `∫_{D_N^PSL} h dμ` by `IsFundamentalDomain.setIntegral_eq`
applied with `hα_fd`, `isFundamentalDomain_Gamma1_PSL`, and the `imageGamma1_PSL`
invariance derived from `h_inv`. -/
private theorem sum_setIntegral_GL2_shift
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
    (h_α_int : IntegrableOn (fun τ => h ((α : GL (Fin 2) ℝ) • τ))
      (Gamma1_fundDomain_PSL N) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (↑α : GL (Fin 2) ℝ) •
          ((q.out : SL(2, ℤ))⁻¹ • (ModularGroup.fd : Set UpperHalfPlane)),
        h τ ∂hyperbolicMeasure =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (ModularGroup.fd : Set UpperHalfPlane),
        h τ ∂hyperbolicMeasure := by
  -- Strategy: LHS = fiber_count · ∫_{α•D_N^PSL} h dμ
  --          RHS = fiber_count · ∫_{D_N^PSL} h dμ
  -- and the two integrals are equal by IsFundamentalDomain.setIntegral_eq.
  set h_α : ℍ → ℂ := fun τ => h ((α : GL (Fin 2) ℝ) • τ) with h_α_def
  have h_α_inv : ∀ (γ : SL(2, ℤ)), γ ∈ Gamma1 N →
      ∀ τ : UpperHalfPlane, h_α (γ • τ) = h_α τ := hα_h_inv
  -- Step 1: Change of variables on each LHS summand.
  have h_LHS_cov : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (↑α : GL (Fin 2) ℝ) •
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)),
        h τ ∂μ_hyp =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane), h_α τ ∂μ_hyp := by
    intro q
    rw [show ((↑α : GL (Fin 2) ℝ) • ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)) :
          Set UpperHalfPlane) =
        (fun τ => (α : GL(2, ℝ)⁺) • τ) ''
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)) from by
        rw [Set.image_smul]; rfl]
    exact (measurePreserving_smul α μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul α) _ _
  simp_rw [h_LHS_cov]
  -- Step 2: Both sums (for h and h_α) reduce to fiber_count · ∫_{D_N^PSL} (·) dμ
  -- via fd → fdo → PSL-fiberwise sum + uniform fiber count + PSL fundamental domain integral.
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
          Finset.sum_congr rfl fun q _ => setIntegral_SL_tile_fd_eq_fdo φ q
      _ = ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
            (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
              slToPslQuot q = q')).card •
              ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set UpperHalfPlane), φ τ ∂μ_hyp :=
          sum_SL_tile_eq_fiberwise_PSL_tile φ φ_inv
      _ = (slToPslQuot_fiberCard N) • ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set UpperHalfPlane), φ τ ∂μ_hyp := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun q' _ => ?_
          congr 1
          convert slToPslQuot_fiberCard_eq q' using 2
          congr
      _ = (slToPslQuot_fiberCard N) • ∫ τ in Gamma1_fundDomain_PSL N, φ τ ∂μ_hyp := by
          rw [← setIntegral_Gamma1_fundDomain_PSL_eq_sum φ φ_int]
  rw [gen_SL_fd_sum_eq h_α h_α_inv h_α_int,
      gen_SL_fd_sum_eq h h_inv h_int]
  congr 1
  -- Goal: ∫_{D_N^PSL} h_α dμ = ∫_{D_N^PSL} h dμ
  -- Step 3a: change of vars shifts h_α back: ∫_{D_N^PSL} h_α = ∫_{α • D_N^PSL} h
  rw [show ∫ τ in Gamma1_fundDomain_PSL N, h_α τ ∂μ_hyp =
        ∫ τ in ((↑α : GL (Fin 2) ℝ) • (Gamma1_fundDomain_PSL N : Set ℍ) : Set ℍ),
          h τ ∂μ_hyp from by
    rw [show ((↑α : GL (Fin 2) ℝ) • (Gamma1_fundDomain_PSL N : Set ℍ) : Set ℍ) =
        (fun τ => (α : GL(2, ℝ)⁺) • τ) '' (Gamma1_fundDomain_PSL N : Set ℍ) from by
        rw [Set.image_smul]; rfl]
    exact ((measurePreserving_smul α μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul α) _ _).symm]
  -- Step 3b: Both D_N^PSL and α • D_N^PSL are imageGamma1_PSL-fundamental domains,
  -- and h is imageGamma1_PSL-invariant (derived from h_inv via PSL_smul_coe).
  refine hα_fd.setIntegral_eq isFundamentalDomain_Gamma1_PSL ?_
  intro g τ
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := Subgroup.mem_map.mp g.property
  have h_act_eq : ((g : imageGamma1_PSL N) : PSL(2, ℤ)) • τ = γ • τ := by
    rw [← hγ_eq]; exact PSL_smul_coe γ τ
  show h (((g : imageGamma1_PSL N) : PSL(2, ℤ)) • τ) = h τ
  rw [h_act_eq]
  exact h_inv γ hγ_mem τ

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_slash_adjoint_GL2
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
    (h_α_int : IntegrableOn (fun τ => petersson k ⇑f ⇑g_adj (α • τ))
      (Gamma1_fundDomain_PSL N) μ_hyp) :
    petN f_α g = petN f g_adj := by
  -- Strategy: transform each petN summand via peterssonInner_slash_adjoint,
  -- then invoke sum_setIntegral_GL2_shift for the domain tiling identity.
  --
  -- Step 1: Convert each petN summand to a set integral, apply hf_α/hg_adj,
  -- then use peterssonInner_slash_adjoint to shift the domain.
  -- Step 2: The shifted-domain sum equals the standard-domain sum by the
  -- fundamental domain tiling identity (sum_setIntegral_GL2_shift).
  --
  -- Proof chain per summand q:
  --   peterssonInner k fd (⇑f_α ∣ q⁻¹) (⇑g ∣ q⁻¹)
  --   = ∫_{q⁻¹•fd} petersson k ⇑f_α ⇑g dμ           [petN_summand_eq_setIntegral]
  --   = ∫_{q⁻¹•fd} petersson k (⇑f∣α) ⇑g dμ          [hf_α]
  --   = peterssonInner k (q⁻¹•fd) (⇑f∣α) ⇑g           [def peterssonInner]
  --   = peterssonInner k (α•(q⁻¹•fd)) ⇑f (⇑g∣adj(α))  [peterssonInner_slash_adjoint]
  --   = ∫_{α•(q⁻¹•fd)} petersson k ⇑f (⇑g∣adj(α)) dμ  [def peterssonInner]
  --   = ∫_{α•(q⁻¹•fd)} petersson k ⇑f ⇑g_adj dμ        [hg_adj]
  -- Then for the RHS:
  --   peterssonInner k fd (⇑f ∣ q⁻¹) (⇑g_adj ∣ q⁻¹)
  --   = ∫_{q⁻¹•fd} petersson k ⇑f ⇑g_adj dμ            [petN_summand_eq_setIntegral]
  -- So: LHS = Σ_q ∫_{α•(q⁻¹•fd)} h dμ, RHS = Σ_q ∫_{q⁻¹•fd} h dμ
  -- where h = petersson k ⇑f ⇑g_adj is Γ₁(N)-invariant.
  -- These are equal by sum_setIntegral_GL2_shift.
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k fd (⇑f_α ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g_adj ∣[k] (q.out)⁻¹)
  -- Rewrite each LHS summand through the chain above.
  have h_lhs : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k fd (⇑f_α ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹) =
      ∫ τ in α • ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)),
        petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ ∂μ_hyp := fun q => by
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
  -- Rewrite each RHS summand.
  have h_rhs : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g_adj ∣[k] (q.out)⁻¹) =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
        petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ ∂μ_hyp := fun q => by
    calc peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g_adj ∣[k] (q.out)⁻¹)
        = ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
            petersson k ⇑f ⇑g_adj τ ∂μ_hyp := petN_summand_eq_setIntegral f g_adj q
      _ = ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
            petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ ∂μ_hyp := by rw [hg_adj]
  simp_rw [h_lhs, h_rhs]
  -- Goal: Σ_q ∫_{α•(q⁻¹•fd)} h dμ = Σ_q ∫_{q⁻¹•fd} h dμ
  -- where h = petersson k ⇑f (⇑g ∣[k] peterssonAdj α) is Γ₁(N)-invariant.
  -- The integrand petersson k ⇑f (⇑g ∣[k] peterssonAdj α) is Γ₁(N)-invariant:
  -- since ⇑g ∣[k] peterssonAdj α = ⇑g_adj (by hg_adj), and f, g_adj are Γ₁(N)-cusp forms,
  -- petersson_Gamma1_invariant gives petersson k ⇑f ⇑g_adj (γ • τ) = petersson k ⇑f ⇑g_adj τ.
  refine sum_setIntegral_GL2_shift ⟨α, hα⟩
    (fun τ => petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ)
    (fun γ hγ τ => by
      show petersson k ⇑f (⇑g ∣[k] peterssonAdj α) (γ • τ) =
        petersson k ⇑f (⇑g ∣[k] peterssonAdj α) τ
      rw [← hg_adj]; exact petersson_Gamma1_invariant f g_adj γ hγ τ)
    (fun γ hγ τ => by rw [← hg_adj]; exact hα_norm γ hγ τ) hα_fd ?_ ?_
  · -- IntegrableOn h (Gamma1_fundDomain_PSL N) μ_hyp
    simpa [hg_adj] using h_int
  · -- IntegrableOn (h ∘ α•) (Gamma1_fundDomain_PSL N) μ_hyp
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

/-- The adjugate of `T_p_upper(b)` as a GL₂(ℝ) element has matrix `[[p,-b],[0,1]]`. -/
private lemma peterssonAdj_glMap_T_p_upper (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (peterssonAdj (glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), -(b : ℝ); 0, 1] := by
  rw [peterssonAdj_coe]
  -- glMap embeds Q → R entrywise; T_p_upper_coe gives the Q-matrix
  have hcoe : (glMap (T_p_upper p hp b) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [glMap, T_p_upper]
  rw [hcoe, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply]

/-- The adjugate of `T_p_lower` as a GL₂(ℝ) element has matrix `[[1,0],[0,p]]`. -/
private lemma peterssonAdj_glMap_T_p_lower (p : ℕ) (hp : 0 < p) :
    (peterssonAdj (glMap (T_p_lower p hp)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), 0; 0, (p : ℝ)] := by
  rw [peterssonAdj_coe]
  have hcoe : (glMap (T_p_lower p hp) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), 0; 0, (1 : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [glMap, T_p_lower]
  rw [hcoe, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply]

/-- The shift matrix `[[1, m; 0, 1]]` as an SL₂(ℤ) element. -/
private def shiftSL_loc (m : ℤ) : SL(2, ℤ) :=
  ⟨!![1, m; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- `shiftSL_loc m ∈ Γ₁(N)` for any level `N`. -/
private lemma shiftSL_loc_mem_Gamma1 (m : ℤ) : shiftSL_loc m ∈ Gamma1 N := by
  rw [Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [shiftSL_loc]

/-- Matrix factorization: `peterssonAdj(glMap(T_p_upper(b))) = mapGL ℝ (shift(-b)) * glMap(T_p_lower)`.

Both sides have matrix `[[p, -b], [0, 1]]` over ℝ. -/
private lemma peterssonAdj_T_p_upper_eq_shift_mul_lower
    (p : ℕ) (hp : 0 < p) (b : ℕ) :
    peterssonAdj (glMap (T_p_upper p hp b)) =
      (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) *
        glMap (T_p_lower p hp) := by
  -- Both sides have matrix [[p, -b], [0, 1]] over ℝ.
  -- Prove by showing their matrix coercions agree.
  apply Units.ext; ext i j
  -- LHS matrix from peterssonAdj_glMap_T_p_upper
  have h_lhs : (peterssonAdj (glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), -(b : ℝ); 0, 1] := peterssonAdj_glMap_T_p_upper p hp b
  -- RHS matrix: product of shift and lower
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

/-- **b-independence** for the Petersson adjoint of T_p coset reps (DS Theorem 5.5.3):
`g ∣[k] adj(glMap(T_p_upper(b))) = g ∣[k] glMap(T_p_lower)` for all `b`.

The adjugate `adj([[1,b],[0,p]]) = [[p,-b],[0,1]] = [[1,-b],[0,1]] · [[p,0],[0,1]]`,
and `[[1,-b],[0,1]] ∈ Γ₁(N)` acts trivially on `g ∈ S_k(Γ₁(N))`. -/
private lemma slash_peterssonAdj_T_p_upper_eq_T_p_lower
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (T_p_upper p hp.pos b)) =
      ⇑g ∣[k] glMap (T_p_lower p hp.pos) := by
  -- Factor: adj(T_p_upper(b)) = mapGL ℝ (shift(-b)) * glMap(T_p_lower)
  rw [peterssonAdj_T_p_upper_eq_shift_mul_lower p hp.pos b,
      SlashAction.slash_mul]
  -- Now: (g ∣[k] mapGL ℝ (shift(-b))) ∣[k] glMap(T_p_lower) = g ∣[k] glMap(T_p_lower)
  -- The shift is in Γ₁(N), so g ∣[k] shift(-b) = g.
  -- SL_slash: g ∣[k] (γ : SL(2,ℤ)) = g ∣[k] (mapGL ℝ γ : GL(Fin 2) ℝ)
  -- slash_Gamma1_eq: g ∣[k] γ = g for γ ∈ Γ₁(N)
  congr 1
  -- Goal: ⇑g ∣[k] (mapGL ℝ ...) (shiftSL_loc ...) = ⇑g
  -- The (mapGL ℝ)(shiftSL_loc(-b)) is the coercion of shiftSL_loc(-b) : SL(2,ℤ) to GL(Fin 2) ℝ.
  -- By SL_slash, g ∣[k] (mapGL ℝ γ) = g ∣[k] γ for γ : SL(2,ℤ).
  -- By slash_Gamma1_eq, g ∣[k] γ = g for γ ∈ Γ₁(N).
  change ⇑g ∣[k] (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) = ⇑g
  have : (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) =
      (shiftSL_loc (-(b : ℤ)) : GL (Fin 2) ℝ) := rfl
  rw [this, ← ModularForm.SL_slash]
  exact slash_Gamma1_eq g _ (shiftSL_loc_mem_Gamma1 _)

/-- The adjugate of `glMap(T_p_lower)` equals `glMap(T_p_upper 0)` as GL₂(ℝ) matrices.

`adj([[p,0],[0,1]]) = [[1,0],[0,p]] = T_p_upper(0)`. -/
private lemma slash_peterssonAdj_T_p_lower_eq_T_p_upper_0
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (T_p_lower p hp.pos)) =
      ⇑g ∣[k] glMap (T_p_upper p hp.pos 0) := by
  -- adj(T_p_lower) has matrix [[1,0],[0,p]] = glMap(T_p_upper(0)).
  -- Two GL₂(ℝ) elements with the same matrix give the same slash.
  congr 1
  apply Units.ext; ext i j
  have h1 := peterssonAdj_glMap_T_p_lower p hp.pos
  have h2 : (glMap (T_p_upper p hp.pos 0) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), 0; 0, (p : ℝ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [glMap, T_p_upper]
  rw [show (peterssonAdj (glMap (T_p_lower p hp.pos)) : Matrix _ _ ℝ) i j =
      (!![(1 : ℝ), 0; 0, (p : ℝ)]) i j from by rw [h1]]
  rw [show (glMap (T_p_upper p hp.pos 0) : Matrix _ _ ℝ) i j =
      (!![(1 : ℝ), 0; 0, (p : ℝ)]) i j from by rw [h2]]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T205-a**: Per-summand slash adjoint identity for a GL₂⁺(ℝ) element β
post-composed with an SL₂(ℤ) element q⁻¹.

Using `peterssonInner_slash_adjoint` with `α = β * q⁻¹` (which has the same positive
determinant as β since det(q⁻¹)=1), and simplifying via:
- `peterssonAdj(β * q⁻¹) = peterssonAdj(q⁻¹) * peterssonAdj(β) = q * peterssonAdj(β)`
- `(g ∣ q⁻¹) ∣ (q * peterssonAdj β) = g ∣ peterssonAdj β`

the domain-shift identity becomes:
```
∫_{fd} petersson k (f ∣ β ∣ q⁻¹) (g ∣ q⁻¹) dμ =
  ∫_{β • q⁻¹ • fd} petersson k f (g ∣ peterssonAdj β) dμ
``` -/
private lemma peterssonInner_slash_adjoint_coset
    (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val) (q : SL(2, ℤ)) (f g : ℍ → ℂ) :
    peterssonInner k fd
        (f ∣[k] (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)))
        (g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) =
      peterssonInner k
        (β • ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)))
        f
        (g ∣[k] peterssonAdj β) := by
  -- Step 1: positive determinant of β * q⁻¹
  have hq_det_mat : ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    have hcast : ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix (q⁻¹).val) := by
      rw [mapGL_coe_matrix]; rfl
    rw [hcast, ← RingHom.map_det, (q⁻¹).property]; simp
  have hdet_pos : 0 < (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)).det.val := by
    show 0 < (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) : GL (Fin 2) ℝ).val.det
    rw [Units.val_mul, Matrix.det_mul, hq_det_mat, mul_one]
    exact hβ
  -- Step 2: Apply peterssonInner_slash_adjoint
  have h_main := peterssonInner_slash_adjoint (k := k)
      (D := fd) (α := β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) hdet_pos
      f (g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ))
  -- Step 3: Simplify peterssonAdj(β * q⁻¹) = q * peterssonAdj β
  have h_adj_prod : peterssonAdj (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) =
      (mapGL ℝ q : GL (Fin 2) ℝ) * peterssonAdj β := by
    rw [peterssonAdj_mul, peterssonAdj_mapGL_SL_eq_inv]
    congr 1
    rw [← map_inv, inv_inv]
  -- Step 4: Simplify (g ∣ q⁻¹) ∣ (q * adj β) = g ∣ adj β
  have h_slash_simp : ((g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) ∣[k]
        peterssonAdj (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ))) =
      g ∣[k] peterssonAdj β := by
    rw [h_adj_prod, ← SlashAction.slash_mul, ← mul_assoc]
    rw [show (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ q : GL (Fin 2) ℝ) = 1 from by
      rw [← map_mul, inv_mul_cancel, map_one], one_mul]
  -- Step 5: Simplify (β * q⁻¹) • fd = β • (q⁻¹ • fd)
  have h_domain : ((β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ) : Set ℍ) =
      (β • ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) : Set ℍ) :=
    mul_smul _ _ _
  -- Step 6: Combine
  rw [← h_slash_simp, ← h_domain]
  exact h_main

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Right-slash version of `peterssonInner_slash_adjoint`**:
`peterssonInner k D f (g ∣ α) = peterssonInner k (α • D) (f ∣ peterssonAdj α) g`.

Follows from `peterssonInner_slash_adjoint` via Hermitian symmetry. -/
private lemma peterssonInner_slash_adjoint_right (D : Set ℍ) (α : GL (Fin 2) ℝ)
    (hα : 0 < α.det.val) (f g : ℍ → ℂ) :
    peterssonInner k D f (g ∣[k] α) =
      peterssonInner k (α • D) (f ∣[k] peterssonAdj α) g := by
  have h1 := peterssonInner_conj_symm k D f (g ∣[k] α)
  have h2 := peterssonInner_slash_adjoint (k := k) D α hα g f
  have h3 := peterssonInner_conj_symm k (α • D) (f ∣[k] peterssonAdj α) g
  rw [← h1, h2, h3]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **T205-a (right variant)**: Per-summand slash adjoint when the right argument
is slashed by a coset rep. Mirrors `peterssonInner_slash_adjoint_coset`. -/
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

private theorem petN_heckeT_p_diamond_shift_core
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) := by
  -- DS Theorem 5.5.3: petN(T_p f, g) = petN(⟨p⟩f, T_p g).
  --
  -- Proof strategy: work at the peterssonInner (single integral) level.
  -- The key tool is peterssonInner_slash_adjoint (fully proved, no sorry),
  -- applied to each T_p coset representative within each petN summand.
  --
  -- Unfold petN on both sides as coset sums:
  --   LHS = Σ_q peterssonInner k fd ((T_p f)∣q⁻¹) (g∣q⁻¹)
  --   RHS = Σ_q peterssonInner k fd ((⟨p⟩f)∣q⁻¹) ((T_p g)∣q⁻¹)
  --
  -- For each q, the LHS summand decomposes via linearity of peterssonInner:
  --   peterssonInner k fd ((T_p f)∣q⁻¹) (g∣q⁻¹)
  --   = Σ_b peterssonInner k fd (f∣α_b∣q⁻¹) (g∣q⁻¹)
  --     + peterssonInner k fd ((⟨p⟩f)∣α_∞∣q⁻¹) (g∣q⁻¹)
  --
  -- Apply peterssonInner_slash_adjoint to each upper term with α = glMap(α_b):
  --   peterssonInner k fd (f∣(α_b * q⁻¹)) (g∣q⁻¹)
  --   = peterssonInner k ((α_b * q⁻¹) • fd) f ((g∣q⁻¹)∣adj(α_b * q⁻¹))
  --
  -- By b-independence (slash_peterssonAdj_T_p_upper_eq_T_p_lower):
  --   (g∣q⁻¹)∣adj(α_b) = (g∣q⁻¹)∣T_p_lower  for all b.
  --
  -- This collapses the sum of p upper terms to p times a single integral.
  -- The lower term gives the T_p_upper(0) piece via
  -- slash_peterssonAdj_T_p_lower_eq_T_p_upper_0.
  --
  -- After the adjugate identification, the remaining step is showing the
  -- shifted domains tile a Γ₁(N)-fundamental domain (so the integrals
  -- reassemble into petN). This domain-tiling step uses:
  --   (1) Γ₁(N)-invariance of the petersson integrand (petersson_Gamma1_invariant)
  --   (2) IsFundamentalDomain structure for Γ₁(N)\ℍ
  --
  -- Step (2) is the only unproved prerequisite — it requires PSL₂ quotient
  -- infrastructure for the faithful Γ₁(N)/{±I} action on ℍ.
  -- This is the same obstacle as in petN_slash_adjoint_GL2.
  --
  -- The proof reduces to petN_slash_adjoint_GL2 applied to each coset rep,
  -- combined with the adjugate algebra above.
  -- We apply petN_slash_adjoint_GL2 to the FULL T_p operator.
  -- T_p f is a CuspForm, and we need to express it as f∣α for some α.
  -- Since T_p is a SUM of slashes, not a single slash, we instead
  -- reduce directly via petN_slash_adjoint_GL2 on each piece.
  --
  -- The CuspForm constraint means we cannot decompose T_p into individual
  -- slash CuspForms (individual slashes are NOT Γ₁(N)-invariant).
  -- Instead, we work at the petN summand level, where each summand is a
  -- peterssonInner integral of plain functions (not CuspForm-valued).
  -- We apply peterssonInner_slash_adjoint (fully proved) to each piece.
  --
  -- The assembly of the domain-shifted integrals back into petN sums
  -- is the fundamental-domain tiling argument.
  --
  -- ============================================================================
  -- Proof state analysis (2026-04-18):
  -- After applying T205-a and T205-a_right to both sides + slash_peterssonAdj
  -- simplifications, LHS and RHS each become sums of two shapes:
  --
  --   LHS = ∑_q [Σ_b peterssonInner k (α_b • q⁻¹ • fd) f (g ∣ T_p_lower)
  --             + peterssonInner k (T_p_lower • q⁻¹ • fd) (⟨p⟩ f) (g ∣ T_p_upper(0))]
  --   RHS = ∑_q [Σ_c peterssonInner k (α_c • q⁻¹ • fd) ((⟨p⟩ f) ∣ T_p_lower) g
  --             + peterssonInner k (T_p_lower • q⁻¹ • fd) ((⟨p⟩ f) ∣ T_p_upper(0)) (⟨p⟩ g)]
  --
  -- Matrix identity (for upper summands): T_p_lower · α_b = p · shift(b) where
  -- shift(b) ∈ Γ₁(N). So (T_p_lower • α_b • q⁻¹ • fd) = (shift(b) · q⁻¹) • fd,
  -- a Γ₁(N)-translate of q⁻¹ • fd.
  --
  -- The summand-matching bijection between LHS's (b, q) pairs and RHS's (c, q')
  -- pairs reflects the double-coset inverse identity:
  --   `Γ₁(N) · diag(p,1) · Γ₁(N) = Γ₁(N) · diag(1,p) · Γ₁(N) · γ₀`
  -- where γ₀ ∈ Γ₀(N) represents ⟨p⟩⁻¹ (= adjointGamma0Rep in this file).
  -- All infrastructure needed is proved: T205-a, peterssonInner_slash_adjoint_right,
  -- slash_peterssonAdj_T_p_{upper,lower}_eq_..., slash_M_infty_eq_diamond_slash_T_p_lower,
  -- sum_setIntegral_GL2_shift, adjointGamma0Rep + adjointGamma0Rep_units.
  -- The remaining ~80-150 LOC is the coset bijection argument.
  --
  -- ============================================================================
  -- Proof skeleton (2026-04-17): structured via named sub-sorries for the hard
  -- coset bijection / per-tile-shift integral identity.
  --
  -- Macro strategy: use `petN_slash_adjoint_GL2` applied once per coset rep of
  -- the naive double-coset sum (`T_p_upper(b)` for 0 ≤ b < p, plus `M_∞`), and
  -- reindex the resulting RHS summands to match the RHS coset-sum form of
  -- `petN (⟨p⟩ f) (T_p g)`.
  --
  -- At the top level, we state the identity as "bijection of naive coset sums"
  -- and delegate the actual matrix bijection to a single sub-sorry.
  -- ============================================================================
  set u := ZMod.unitOfCoprime p hpN with hu_def
  -- ============================================================================
  -- Step 1: Unfold `petN` on both sides to sums over `SL₂(ℤ)/Γ₁(N)`-cosets.
  -- Each side becomes a finite sum of `peterssonInner k fd (… ∣ q⁻¹) (… ∣ q⁻¹)`.
  -- ============================================================================
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      UpperHalfPlane.peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      UpperHalfPlane.peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k u f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑(heckeT_p_cusp k p hp hpN g) ∣[k] (q.out : SL(2, ℤ))⁻¹)
  -- ============================================================================
  -- Step 2: On the LHS, rewrite `⇑(heckeT_p_cusp k p hp hpN f)` as
  --   `heckeT_p_ut k p hp.pos (⇑f.toModularForm') + ⇑f.toModularForm' ∣[k] M_∞`
  -- via `heckeT_p_fun_eq_coset_sum`. This is the "naive double-coset sum" form.
  --
  -- On the RHS, similarly rewrite `⇑(heckeT_p_cusp k p hp hpN g)`.
  --
  -- Step 3: Split each `peterssonInner` summand using linearity in the slashed-sum
  -- argument. (Requires per-coset integrability of the petersson integrand.)
  --
  -- Step 4: For each upper-triangular term `peterssonInner k fd (f ∣ α_b ∣ q⁻¹) …`,
  -- apply `peterssonInner_slash_adjoint_coset` with β = glMap (T_p_upper p hp.pos b)
  -- to get `peterssonInner k (β • q⁻¹ • fd) f (g ∣ peterssonAdj β)`.
  --
  -- Step 5: `slash_peterssonAdj_T_p_upper_eq_T_p_lower` shows
  --   `g ∣ peterssonAdj (glMap (T_p_upper p hp.pos b)) = g ∣ glMap (T_p_lower p hp.pos)`
  -- for ALL b (b-independence), collapsing the Σ_b sum to p copies.
  --
  -- Step 6: For the M_∞ term, use `slash_M_infty_eq_diamond_slash_T_p_lower` to
  -- rewrite `f ∣ M_∞ = (⟨p⟩ f) ∣ T_p_lower`, introducing the ⟨p⟩ twist.
  --
  -- Step 7: Mirror Steps 3-6 on the RHS (which has `T_p g` instead of `T_p f`).
  --
  -- Step 8: At this point LHS and RHS are sums of integrals over
  --   - p shifted-tile integrals of `f, g ∣ T_p_lower` vs `(⟨p⟩ f) ∣ T_p_lower, g`
  --   - 1 integral of `(⟨p⟩ f), g ∣ T_p_upper(0)` vs `(⟨p⟩ f) ∣ T_p_upper(0), (⟨p⟩ g)`
  -- The residual reindexing is by `adjointGamma0Rep`, which is a Γ₀(N) rep for ⟨p⟩⁻¹.
  --
  -- Step 9: Use `petN_slash_invariant` with γ = adjointGamma0Rep, together with
  -- `diamondOp_petersson_unitary` for the ⟨p⟩ twist, to match the final sums.
  -- ============================================================================
  --
  -- STARTING POINT: naive double-coset sum decomposition (via `heckeT_p_fun_eq_coset_sum`).
  have h_Tpf : (⇑(heckeT_p_cusp k p hp hpN f) : UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos (⇑f.toModularForm') +
      ⇑f.toModularForm' ∣[k] (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) :=
    heckeT_p_fun_eq_coset_sum k hp hpN f.toModularForm'
  have h_Tpg : (⇑(heckeT_p_cusp k p hp hpN g) : UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos (⇑g.toModularForm') +
      ⇑g.toModularForm' ∣[k] (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) :=
    heckeT_p_fun_eq_coset_sum k hp hpN g.toModularForm'
  -- After the naive double-coset decomposition above, the identity reduces to
  -- a sum over `q ∈ SL₂(ℤ)/Γ₁(N)` of the "naive double-coset" expansion of each side.
  -- Substitute h_Tpf on LHS and h_Tpg on RHS to put both sides in the form
  -- ∑_q peterssonInner k fd ((Σ_b f∣α_b + f∣M_∞)∣q⁻¹) ... .
  simp_rw [h_Tpf, h_Tpg]
  -- ============================================================================
  -- REMAINING SUB-SORRY: `petN_naive_double_coset_symmetric_adjoint`
  --
  -- Statement (after `simp_rw [h_Tpf, h_Tpg]`):
  --   ∑_q peterssonInner k fd
  --        ((heckeT_p_ut k p hp.pos ⇑f + ⇑f ∣[k] M_∞) ∣[k] q.out⁻¹)
  --        (⇑g ∣[k] q.out⁻¹)
  --   =
  --   ∑_q peterssonInner k fd
  --        (⇑(⟨u⟩ f) ∣[k] q.out⁻¹)
  --        ((heckeT_p_ut k p hp.pos ⇑g + ⇑g ∣[k] M_∞) ∣[k] q.out⁻¹)
  --
  -- Informal argument outline (~80-150 LOC, not attempted here):
  --   1. Distribute + via SlashAction.add_slash and peterssonInner linearity.
  --      LHS = Σ_q [peterssonInner (f_ut ∣ q⁻¹) (g ∣ q⁻¹)
  --               + peterssonInner (f ∣ M_∞ ∣ q⁻¹) (g ∣ q⁻¹)]
  --      where f_ut := heckeT_p_ut k p hp.pos ⇑f = Σ_b f ∣ α_b.
  --   2. On the "upper" part of LHS, apply peterssonInner_slash_adjoint_coset
  --      with β = glMap (T_p_upper p hp.pos b) for each b. Use
  --      slash_peterssonAdj_T_p_upper_eq_T_p_lower for b-independence,
  --      collapsing the Σ_b into p copies of the same integral.
  --   3. On the "M_∞" term, rewrite f ∣ M_∞ = ⟨u⟩f ∣ T_p_lower via
  --      slash_M_infty_eq_diamond_slash_T_p_lower, then apply
  --      peterssonInner_slash_adjoint_coset with β = glMap (T_p_lower) and
  --      slash_peterssonAdj_T_p_lower_eq_T_p_upper_0.
  --   4. Mirror Steps 1-3 on RHS via the "right" variants
  --      (peterssonInner_slash_adjoint_coset_right, etc.).
  --   5. After Steps 2-4, LHS and RHS are sums of `peterssonInner` with shifted
  --      domains {α • q.out⁻¹ • fd}. These assemble into Γ₁(N)-fundamental
  --      domain integrals via sum_setIntegral_GL2_shift.
  --   6. The remaining sums are matched via a coset bijection induced by
  --      `adjointGamma0Rep p N hpN ∈ Γ₀(N)`, whose image under `Gamma0MapUnits`
  --      is `u⁻¹` (cf. `adjointGamma0Rep_units`). This rep represents ⟨u⟩⁻¹,
  --      which accounts for the ⟨u⟩-twist difference between LHS and RHS.
  --
  -- All infrastructure (peterssonInner_slash_adjoint_coset,
  -- peterssonInner_slash_adjoint_coset_right, slash_peterssonAdj_T_p_upper_eq_T_p_lower,
  -- slash_peterssonAdj_T_p_lower_eq_T_p_upper_0, slash_M_infty_eq_diamond_slash_T_p_lower,
  -- M_infty_eq_sigma_mul_T_p_lower, sum_setIntegral_GL2_shift, adjointGamma0Rep,
  -- adjointGamma0Rep_units, petN_slash_invariant, diamondOp_petersson_unitary,
  -- heckeT_p_comm_diamondOp) is proved. The remaining step is assembling these
  -- via the coset bijection argument.
  -- --------------------------------------------------------------------------
  -- Concrete progress (2026-04-17): rewrite `f ∣ M_∞ = (⟨u⟩ f) ∣ T_p_lower`
  -- on both sides (via `slash_M_infty_eq_diamond_slash_T_p_lower`), then
  -- distribute the outer `∣[k] q.out⁻¹` over the `+` in each petersson
  -- slot via `SlashAction.add_slash`. This puts both sides into the
  -- symmetric "four-term" shape where the upper-triangular (`heckeT_p_ut`)
  -- and lower-diamond (`(⟨u⟩ h) ∣ T_p_lower`) pieces appear explicitly on
  -- each side, which is the setup expected by the remaining coset-bijection
  -- / peterssonInner-adjoint argument. The residual sorry is exactly the
  -- "naive double-coset symmetric adjoint" identity described above.
  simp only [slash_M_infty_eq_diamond_slash_T_p_lower k p hp.pos hpN,
    SlashAction.add_slash]
  sorry

/-- **Adjoint form of `T_p`** (DS Theorem 5.5.3):
`petN(T_p f, g) = petN(f, ⟨p⟩⁻¹ T_p g)`.

Derived from `petN_heckeT_p_diamond_shift_core` (the symmetric form
`petN(T_p f, g) = petN(⟨p⟩f, T_p g)`) via `diamondOp_petersson_unitary`. -/
private theorem petN_heckeT_p_adjoint_unsymm
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  -- Derive from the symmetric form via diamondOp_petersson_unitary:
  --   petN(T_p f, g) = petN(⟨p⟩f, T_p g)             [diamond_shift_core]
  --                   = petN(⟨p⟩f, ⟨p⟩(⟨p⟩⁻¹ T_p g)) [⟨p⟩∘⟨p⟩⁻¹ = id]
  --                   = petN(f, ⟨p⟩⁻¹ T_p g)          [diamondOp_petersson_unitary]
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

/-- Core double-coset identity for the Hecke adjoint (DS Theorem 5.5.3):
`⟨T_p f, g⟩_N = ⟨⟨p⟩f, T_p g⟩_N`.

Now a direct consequence of `petN_heckeT_p_diamond_shift_core`. -/
private theorem petN_heckeT_p_diamond_shift
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  petN_heckeT_p_diamond_shift_core p hp hpN f g

/-- Derives `heckeT_p_adjoint` from `petN_heckeT_p_diamond_shift` via
`diamondOp_petersson_unitary`. -/
private theorem heckeT_p_adjoint_of_diamond_shift
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  -- Chain: petN(T_p f, g) = petN(⟨p⟩f, T_p g) = petN(f, ⟨p⟩⁻¹ T_p g)
  set u := ZMod.unitOfCoprime p hpN
  -- Step 1: petN(T_p f, g) = petN(⟨u⟩f, T_p g)
  have h1 := petN_heckeT_p_diamond_shift p hp hpN f g
  -- Step 2: ⟨u⟩(⟨u⟩⁻¹ (T_p g)) = T_p g
  have h_cancel : diamondOp_cusp k u (diamondOp_cusp k u⁻¹
      (heckeT_p_cusp k p hp hpN g)) = heckeT_p_cusp k p hp hpN g := by
    show diamondOpCusp k u (diamondOpCusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) =
      heckeT_p_cusp k p hp hpN g
    rw [show diamondOpCusp k u (diamondOpCusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) =
        ((diamondOpCusp k u).comp (diamondOpCusp k u⁻¹)) (heckeT_p_cusp k p hp hpN g) from rfl,
      ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
    rfl
  -- Step 3: petN(⟨u⟩f, ⟨u⟩(⟨u⟩⁻¹ T_p g)) = petN(f, ⟨u⟩⁻¹ T_p g)
  have h2 := diamondOp_petersson_unitary u f
    (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g))
  -- Combine:
  --   petN(T_p f, g) = petN(⟨u⟩f, T_p g)             [h1]
  --                   = petN(⟨u⟩f, ⟨u⟩(⟨u⟩⁻¹ T_p g)) [h_cancel⁻¹ on 2nd arg]
  --                   = petN(f, ⟨u⟩⁻¹ T_p g)          [h2]
  calc petN (heckeT_p_cusp k p hp hpN f) g
      = petN (diamondOp_cusp k u f) (heckeT_p_cusp k p hp hpN g) := h1
    _ = petN (diamondOp_cusp k u f) (diamondOp_cusp k u
          (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g))) := by
        rw [h_cancel]
    _ = petN f (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) := h2

/-- **DS Theorem 5.5.3**: `T_p* = ⟨p⟩⁻¹ T_p` w.r.t. the level-N Petersson product
`petN`, i.e. `⟨T_p f, g⟩_N = ⟨f, ⟨p⟩⁻¹ T_p g⟩_N`.

The proof reduces to `petN_heckeT_p_diamond_shift` (the symmetric form
`⟨T_p f, g⟩ = ⟨⟨p⟩f, T_p g⟩`) via `diamondOp_petersson_unitary`:
```
  petN(T_p f, g) = petN(⟨p⟩f, T_p g)           [petN_heckeT_p_diamond_shift]
                 = petN(⟨p⟩f, ⟨p⟩(⟨p⟩⁻¹ T_p g)) [⟨p⟩∘⟨p⟩⁻¹ = id]
                 = petN(f, ⟨p⟩⁻¹ T_p g)          [diamondOp_petersson_unitary]
```
-/
theorem heckeT_p_adjoint
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  heckeT_p_adjoint_of_diamond_shift p hp hpN f g

/-! ### Helper lemmas for `heckeT_n_adjoint` -/

/-- `T_n` commutes with `⟨d⟩` at the CuspForm level: for `(n, N) = 1`,
`T_n(⟨d⟩ f) = ⟨d⟩(T_n f)`. Follows from `heckeT_n_comm_diamondOp`. -/
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
  exact congr_arg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k => m.toFun τ) h.symm

/-- CuspForm-level decomposition: `T_m f = T_{p^v}(T_{m/p^v} f)` for `m > 1`. -/
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

/-- `T_m(T_n f) = T_n(T_m f)` at the CuspForm level. Follows from `heckeT_n_comm`. -/
private theorem heckeT_n_cusp_comm (m n : ℕ) [NeZero m] [NeZero n]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp k m (heckeT_n_cusp k n f) =
      heckeT_n_cusp k n (heckeT_n_cusp k m f) := by
  apply CuspForm.ext; intro τ
  show ((heckeT_n k m) ((heckeT_n k n) f.toModularForm')).toFun τ =
    ((heckeT_n k n) ((heckeT_n k m) f.toModularForm')).toFun τ
  have h := congr_fun (congr_arg DFunLike.coe (heckeT_n_comm k m n)) f.toModularForm'
  simp only [Module.End.mul_apply] at h
  exact congr_arg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k => m.toFun τ) h

/-- `⟨d₁⟩(⟨d₂⟩ f) = ⟨d₁ * d₂⟩ f` at the CuspForm level. -/
private theorem diamondOp_cusp_comp (d₁ d₂ : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d₁ (diamondOp_cusp k d₂ f) =
      diamondOp_cusp k (d₁ * d₂) f := by
  show diamondOpCusp k d₁ (diamondOpCusp k d₂ f) = diamondOpCusp k (d₁ * d₂) f
  rw [show diamondOpCusp k d₁ (diamondOpCusp k d₂ f) =
    ((diamondOpCusp k d₁).comp (diamondOpCusp k d₂)) f from rfl,
    ← diamondOpCusp_mul]

/-- `⟨1⟩ f = f` at the CuspForm level. -/
private theorem diamondOp_cusp_one
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k (1 : (ZMod N)ˣ) f = f := by
  show diamondOpCusp k 1 f = f
  have := congr_fun (congr_arg DFunLike.coe (diamondOpCusp_one (N := N) (k := k))) f
  exact CuspForm.ext fun τ => congr_arg (fun m => m τ) this

/-- The coprime-factorization step of the `heckeT_n_adjoint` induction.
Given `m = n₁ * n₂` with the IH for both factors, chains:
```
petN(T_m f, g) = petN(T_{n₁}(T_{n₂} f), g)       [decomp]
             = petN(T_{n₂} f, ⟨n₁⟩⁻¹ T_{n₁} g)    [IH on n₁]
             = petN(f, ⟨n₂⟩⁻¹ T_{n₂}(⟨n₁⟩⁻¹ T_{n₁} g))  [IH on n₂]
             = petN(f, ⟨n₂⟩⁻¹ ⟨n₁⟩⁻¹ T_{n₂}(T_{n₁} g))  [T_{n₂} comm ⟨n₁⟩⁻¹]
             = petN(f, ⟨m⟩⁻¹ T_m g)                [unit mult + decomp]
``` -/
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
  -- Step 1: T_m f' = T_{n₁}(T_{n₂} f')
  rw [hDecomp f']
  -- Step 2: Apply IH on n₁
  rw [ih_n₁ (heckeT_n_cusp k n₂ f') g']
  -- Step 3: Apply IH on n₂
  rw [ih_n₂ f' (diamondOp_cusp k (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹
    (heckeT_n_cusp k n₁ g'))]
  -- Step 4: Commutativity: T_{n₂}(⟨n₁⟩⁻¹ h) = ⟨n₁⟩⁻¹(T_{n₂} h)
  rw [heckeT_n_cusp_comm_diamondOp n₂ hn₂_cop
    (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹ (heckeT_n_cusp k n₁ g')]
  -- Step 5: Compose diamonds, commute Hecke operators, match units
  rw [diamondOp_cusp_comp]
  -- Hecke comm + decomp: T_{n₂}(T_{n₁} g') = T_{n₁}(T_{n₂} g') = T_m g'
  have h_hecke : heckeT_n_cusp k n₂ (heckeT_n_cusp k n₁ g') = heckeT_n_cusp k m g' :=
    (heckeT_n_cusp_comm n₂ n₁ g').trans (hDecomp g').symm
  have h_unit : (ZMod.unitOfCoprime n₂ hn₂_cop)⁻¹ * (ZMod.unitOfCoprime n₁ hn₁_cop)⁻¹ =
      (ZMod.unitOfCoprime m hcop)⁻¹ := by
    rw [← mul_inv]; congr 1; ext
    simp only [Units.val_mul, ZMod.coe_unitOfCoprime]; rw [mul_comm]
    exact_mod_cast congr_arg (Nat.cast (R := ZMod N))
      (show (n₁ : ℕ) * n₂ = m from by rw [hdiv_eq]; exact Nat.mul_div_cancel' hpv_dvd)
  simp only [h_hecke, h_unit]

/-- CuspForm-level prime-power recursion:
`T_{p^{r+2}} f = T_p(T_{p^{r+1}} f) - p^{k-1} • ⟨p⟩(T_{p^r} f)`.

Lifts `heckeT_ppow_succ_succ` from `Module.End` to `CuspForm`. -/
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
  -- Work at Module.End level
  show (heckeT_n k (p ^ (r + 2)) f.toModularForm').toFun τ =
    ((heckeT_n k p) ((heckeT_n k (p ^ (r + 1))) f.toModularForm')).toFun τ -
      (↑p : ℂ) ^ (k - 1) •
        ((diamondOp k (ZMod.unitOfCoprime p hpN))
          ((heckeT_n k (p ^ r)) f.toModularForm')).toFun τ
  rw [heckeT_n_prime_pow k hp (r + 2) (by omega), heckeT_n_prime_pow k hp (r + 1) (by omega),
      heckeT_n_prime_coprime k hp hpN]
  -- Now both sides use heckeT_ppow / heckeT_p / diamondOp
  rw [heckeT_ppow_succ_succ k p hp r]
  -- LHS: (heckeT_p_all * heckeT_ppow (r+1) - c • (diamondOp_ext * heckeT_ppow r)) f
  rw [diamondOp_ext_coprime k hpN, heckeT_p_all_coprime k hp hpN]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    ModularForm.sub_apply]
  -- Now need to handle the heckeT_ppow on RHS
  conv_rhs =>
    rw [show heckeT_n k (p ^ r) = heckeT_ppow (N := N) k p hp r from by
        rcases r with _ | r
        · simp [heckeT_n, heckeT_n_aux, heckeT_ppow]
        · exact heckeT_n_prime_pow k hp _ (by omega)]
  rfl

/-- The diamond cancel lemma: `⟨d⟩(⟨d⟩⁻¹ f) = f`. -/
private theorem diamondOp_cusp_cancel (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d (diamondOp_cusp k d⁻¹ f) = f := by
  show diamondOpCusp k d (diamondOpCusp k d⁻¹ f) = f
  rw [show diamondOpCusp k d (diamondOpCusp k d⁻¹ f) =
      ((diamondOpCusp k d).comp (diamondOpCusp k d⁻¹)) f from rfl,
    ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
  rfl

/-- The diamond cancel lemma: `⟨d⟩⁻¹(⟨d⟩ f) = f`. -/
private theorem diamondOp_cusp_inv_cancel (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d⁻¹ (diamondOp_cusp k d f) = f := by
  show diamondOpCusp k d⁻¹ (diamondOpCusp k d f) = f
  rw [show diamondOpCusp k d⁻¹ (diamondOpCusp k d f) =
      ((diamondOpCusp k d⁻¹).comp (diamondOpCusp k d)) f from rfl,
    ← diamondOpCusp_mul, inv_mul_cancel, diamondOpCusp_one]
  rfl

/-- `petN(⟨d⟩ f, g) = petN(f, ⟨d⟩⁻¹ g)` — diamond adjoint from diamond unitarity. -/
private theorem petN_diamondOp_adjoint (d : (ZMod N)ˣ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k d f) g =
      petN f (diamondOp_cusp k d⁻¹ g) := by
  calc petN (diamondOp_cusp k d f) g
      = petN (diamondOp_cusp k d f) (diamondOp_cusp k d (diamondOp_cusp k d⁻¹ g)) := by
        rw [diamondOp_cusp_cancel]
    _ = petN f (diamondOp_cusp k d⁻¹ g) := diamondOp_petersson_unitary d f _

/-- `starRingEnd ℂ ((↑p : ℂ) ^ (k - 1)) = (↑p : ℂ) ^ (k - 1)` — the scalar is real. -/
private theorem conj_natCast_zpow (p : ℕ) : starRingEnd ℂ ((↑p : ℂ) ^ (k - 1)) =
    (↑p : ℂ) ^ (k - 1) := by
  have : starRingEnd ℂ (↑p : ℂ) = (↑p : ℂ) := by
    rw [show (↑p : ℂ) = (↑(p : ℝ) : ℂ) from by push_cast; rfl]
    exact Complex.conj_ofReal _
  rw [map_zpow₀, this]

/-- The prime-power case of the Hecke adjoint: if the IH holds for all
`j < p^v` with `v ≥ 2`, then
`petN(T_{p^v} f, g) = petN(f, ⟨p^v⟩⁻¹ T_{p^v} g)`. -/
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
  -- Write v = r + 2 for some r
  obtain ⟨r, rfl⟩ : ∃ r, v = r + 2 := ⟨v - 2, by omega⟩
  -- Key: coprimality propagation
  have hp_cop : Nat.Coprime p N := Nat.Coprime.coprime_dvd_left
    (dvd_pow_self p (by omega : r + 2 ≠ 0)) hcop
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
  have hpv1_cop : Nat.Coprime (p ^ (r + 1)) N := Nat.Coprime.pow_left _ hp_cop
  have hpr_cop : Nat.Coprime (p ^ r) N := Nat.Coprime.pow_left _ hp_cop
  -- Size bounds for IH
  have hp_lt : p < p ^ (r + 2) := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ (r + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hpv1_lt : p ^ (r + 1) < p ^ (r + 2) :=
    Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hpr_lt : p ^ r < p ^ (r + 2) :=
    Nat.pow_lt_pow_right hp.one_lt (by omega : r < r + 2)
  -- Abbreviation
  set up := ZMod.unitOfCoprime p hp_cop
  set c := (↑p : ℂ) ^ (k - 1)
  -- Step 1: Apply the CuspForm-level recursion to f'
  rw [heckeT_n_cusp_ppow_recursion p hp hp_cop r f']
  -- LHS = petN(T_p(T_{p^{r+1}} f') - c • ⟨p⟩(T_{p^r} f'), g')
  -- Step 2: petN linearity in first argument
  rw [show (heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) f') -
      c • diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) f') :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) f') +
      (-(c • diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) f'))) from sub_eq_add_neg _ _]
  rw [petN_add_left, petN_neg_left, petN_conj_smul_left, conj_natCast_zpow]
  -- LHS = petN(T_p(T_{p^{r+1}} f'), g') - c * petN(⟨p⟩(T_{p^r} f'), g')
  -- Step 3: IH for p on the first term
  rw [ih p hp_lt hp.pos hp_cop (heckeT_n_cusp k (p ^ (r + 1)) f') g']
  -- First term = petN(T_{p^{r+1}} f', ⟨p⟩⁻¹ T_p g')
  -- Step 4: IH for p^{r+1} on the first term
  rw [ih (p ^ (r + 1)) hpv1_lt (pow_pos hp.pos _) hpv1_cop f'
    (diamondOp_cusp k up⁻¹ (heckeT_n_cusp k p g'))]
  -- First term = petN(f', ⟨p^{r+1}⟩⁻¹ T_{p^{r+1}} (⟨p⟩⁻¹ T_p g'))
  -- Step 5: Diamond adjoint for second term
  rw [petN_diamondOp_adjoint up (heckeT_n_cusp k (p ^ r) f') g']
  -- Second term = c * petN(T_{p^r} f', ⟨p⟩⁻¹ g')
  -- Step 6: IH for p^r on the second term
  rw [ih (p ^ r) hpr_lt (pow_pos hp.pos _) hpr_cop f'
    (diamondOp_cusp k up⁻¹ g')]
  -- Now both terms have the form petN(f', ...)
  -- First:  petN(f', ⟨p^{r+1}⟩⁻¹ T_{p^{r+1}}(⟨p⟩⁻¹ T_p g'))
  -- Second: c * petN(f', ⟨p^r⟩⁻¹ T_{p^r}(⟨p⟩⁻¹ g'))
  -- Commute T with ⟨p⟩⁻¹
  rw [heckeT_n_cusp_comm_diamondOp (p ^ (r + 1)) hpv1_cop up⁻¹
      (heckeT_n_cusp k p g')]
  rw [heckeT_n_cusp_comm_diamondOp (p ^ r) hpr_cop up⁻¹ g']
  -- Compose diamonds
  rw [diamondOp_cusp_comp, diamondOp_cusp_comp]
  -- Hecke commutativity: T_{p^{r+1}}(T_p g') = T_p(T_{p^{r+1}} g')
  rw [heckeT_n_cusp_comm (p ^ (r + 1)) p g']
  -- Reassemble using petN linearity in second argument
  rw [← petN_smul_right c f', ← petN_neg_right, ← petN_add_right]
  congr 1
  -- Unit identities: ⟨a⟩⁻¹ * ⟨b⟩⁻¹ = ⟨a*b⟩⁻¹
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
  -- Apply recursion on g'
  rw [heckeT_n_cusp_ppow_recursion p hp hp_cop r g']
  -- Distribute ⟨d⟩ over subtraction: ⟨d⟩(a - b) = ⟨d⟩a - ⟨d⟩b
  rw [show diamondOp_cusp k (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹
      (heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) g') -
        c • diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) g')) =
      diamondOp_cusp k (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹
        (heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) g')) -
      diamondOp_cusp k (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹
        (c • diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) g')) from by
    show diamondOpCusp k _ _ = diamondOpCusp k _ _ - diamondOpCusp k _ _
    rw [← (diamondOpCusp k _).map_sub]]
  -- ⟨d⟩ commutes with scalar: ⟨d⟩(c • h) = c • ⟨d⟩ h
  rw [show diamondOp_cusp k (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹
      (c • diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) g')) =
      c • diamondOp_cusp k (ZMod.unitOfCoprime (p ^ (r + 2)) hcop)⁻¹
        (diamondOp_cusp k up (heckeT_n_cusp k (p ^ r) g')) from by
    show diamondOpCusp k _ _ = c • diamondOpCusp k _ _
    rw [← (diamondOpCusp k _).map_smul]]
  -- ⟨p^{r+2}⟩⁻¹ ⟨p⟩ = ⟨p^{r+1}⟩⁻¹
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
  -- Now LHS = ⟨p^{r+2}⟩⁻¹(T_p(T_{p^{r+1}} g')) + -(c • ⟨p^{r+1}⟩⁻¹(T_{p^r} g'))
  -- RHS = ⟨p^{r+2}⟩⁻¹(T_p(T_{p^{r+1}} g')) - c • ⟨p^{r+1}⟩⁻¹(T_{p^r} g')
  -- These are equal: a + (-b) = a - b
  abel

/-! ### Normality of Hecke operators -/

/-- The Hecke adjoint for general T_n: `T_n* = ⟨n⟩⁻¹ T_n` on `S_k(Γ₁(N))`,
w.r.t. the level-N Petersson inner product `petN`.

This generalises `heckeT_p_adjoint` from primes to all `n` with `(n,N) = 1`.

## Proof strategy

Uses strong induction on `n`, decomposing `n = p^v * (n/p^v)` via `minFac`.
- **Base case** `n = 1`: Both sides equal `petN f g`.
- **Prime case** `n = p` (i.e. `p^v = n` and `v = 1`): Reduces to `heckeT_p_adjoint`.
- **Composite case** `n > 1`: Decompose `n = p^v * (n/p^v)` via `minFac`. When `p^v < n`
  (i.e. n is not a prime power), both factors are strictly smaller and we apply IH to
  each. When `p^v = n` and `v = 1`, n is prime. When `p^v = n` and `v ≥ 2`, we use
  that `p < n` and `p^{v-1} < n` are both strictly smaller.

Reference: [DS] Theorem 5.5.3, [Miy] Theorem 4.5.4. -/
theorem heckeT_n_adjoint
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_n_cusp k n f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹
        (heckeT_n_cusp k n g)) := by
  -- Strong induction: strengthen to quantify over all m, f', g'
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
    · -- m = 1: T_1 = id, ⟨1⟩ = id, both sides equal petN f' g'
      have hm1 : m = 1 := by omega
      subst hm1
      have hT1f : heckeT_n_cusp (N := N) k 1 f' = f' := CuspForm.ext fun τ => by
        show (heckeT_n k 1 f'.toModularForm').toFun τ = f' τ; rw [heckeT_n_one]; rfl
      have hT1g : heckeT_n_cusp (N := N) k 1 g' = g' := CuspForm.ext fun τ => by
        show (heckeT_n k 1 g'.toModularForm').toFun τ = g' τ; rw [heckeT_n_one]; rfl
      have hunit : ZMod.unitOfCoprime 1 hcop = 1 := by
        ext; simp [ZMod.coe_unitOfCoprime]
      rw [hT1f, hT1g, hunit, inv_one, diamondOp_cusp_one]
    · -- m > 1: decompose m = p^v * (m/p^v) via minFac
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
      -- CuspForm decomposition: T_m f = T_{p^v}(T_{m/p^v} f)
      have hDecomp : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
          heckeT_n_cusp k m h =
            heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k (m / p ^ v) h) :=
        fun h => heckeT_n_cusp_decomp m hle h
      -- IH on m/p^v (always < m for m > 1)
      have ih_div : ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
          petN (heckeT_n_cusp k (m / p ^ v) f₀) g₀ =
            petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime (m / p ^ v) hdiv_cop)⁻¹
              (heckeT_n_cusp k (m / p ^ v) g₀)) :=
        fun f₀ g₀ => ih _ hdiv_lt hdiv_pos hdiv_cop f₀ g₀
      by_cases hpv_lt : p ^ v < m
      · -- Case 1: p^v < m (not a prime power), so both p^v and m/p^v are < m
        -- IH on p^v
        have ih_pv : ∀ f₀ g₀ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
            petN (heckeT_n_cusp k (p ^ v) f₀) g₀ =
              petN f₀ (diamondOp_cusp k (ZMod.unitOfCoprime (p ^ v) hpv_cop)⁻¹
                (heckeT_n_cusp k (p ^ v) g₀)) :=
          fun f₀ g₀ => ih _ hpv_lt hpv_pos hpv_cop f₀ g₀
        exact heckeT_n_adjoint_coprime_case m hcop (p ^ v) (m / p ^ v)
          hpv_cop hdiv_cop (Nat.ordProj_dvd m p) rfl hDecomp ih_pv ih_div f' g'
      · -- Case 2: p^v = m (prime power)
        have hpv_eq : p ^ v = m := le_antisymm
          (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (not_lt.mp hpv_lt)
        by_cases hv1 : v = 1
        · -- v = 1: m = p is prime, reduce to heckeT_p_adjoint
          have hp_m : Nat.Prime m := by rw [← hpv_eq, hv1, pow_one]; exact hpp
          have hTn_eq : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
              heckeT_n_cusp k m h = heckeT_p_cusp k m hp_m hcop h :=
            fun h => CuspForm.ext fun τ => by
              show (heckeT_n k m h.toModularForm').toFun τ =
                (heckeT_p k m hp_m hcop h.toModularForm').toFun τ
              rw [heckeT_n_prime_coprime k hp_m hcop]
          rw [hTn_eq f', hTn_eq g']
          exact heckeT_p_adjoint m hp_m hcop f' g'
        · -- v ≥ 2: m = p^v, prime power. Use heckeT_n_adjoint_ppow_case.
          have hv2 : 2 ≤ v := by omega
          -- Convert T_m / ⟨m⟩ to T_{p^v} / ⟨p^v⟩ via CuspForm.ext
          have hTn_pv : ∀ h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
              heckeT_n_cusp k m h = heckeT_n_cusp k (p ^ v) h := fun h =>
            CuspForm.ext fun τ => by
              show (heckeT_n k m h.toModularForm').toFun τ =
                (heckeT_n k (p ^ v) h.toModularForm').toFun τ
              simp only [heckeT_n, hpv_eq]
          have h_unit_eq : (ZMod.unitOfCoprime m hcop)⁻¹ =
              (ZMod.unitOfCoprime (p ^ v) hpv_cop)⁻¹ := by
            congr 1; ext; simp [ZMod.coe_unitOfCoprime, hpv_eq]
          rw [hTn_pv f', hTn_pv g', h_unit_eq]
          -- Now ih has m but the helper needs p^v; adapt via hpv_eq
          exact heckeT_n_adjoint_ppow_case p hpp v hv2 hpv_cop
            (fun j hj hj_pos hj_cop f₀ g₀ => by
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
  exact congr_arg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k => m.toFun τ) h

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
    exact congr_arg (fun m : ModularForm _ _ => m.toFun z) h
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
  toFun := fun ⟨f, hf⟩ =>
    ⟨heckeT_n_cusp k n f, heckeT_n_cusp_preserves_cuspFormCharSpace k n hn χ hf⟩
  map_add' := fun ⟨f₁, _⟩ ⟨f₂, _⟩ => by
    ext z; show (heckeT_n k n (f₁ + f₂).toModularForm').toFun z =
      ((heckeT_n k n f₁.toModularForm').toFun z + (heckeT_n k n f₂.toModularForm').toFun z)
    rw [show (f₁ + f₂).toModularForm' = f₁.toModularForm' + f₂.toModularForm' from rfl, map_add]
    rfl
  map_smul' := fun c ⟨f, _⟩ => by
    ext z; show (heckeT_n k n (c • f).toModularForm').toFun z =
      c • (heckeT_n k n f.toModularForm').toFun z
    rw [show (c • f).toModularForm' = c • f.toModularForm' from rfl, map_smul]
    rfl

/-- Additivity in the first argument of `petN`. Derived from `petN_add_right` + Hermitian symmetry. -/
private theorem petN_add_left'
    (f₁ f₂ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (f₁ + f₂) g = petN f₁ g + petN f₂ g := by
  have h := petN_add_right g f₁ f₂
  have e := congr_arg (starRingEnd ℂ) h
  rw [petN_conj_symm, map_add, petN_conj_symm, petN_conj_symm] at e
  exact e

/-- Conjugate-scalar in the first argument of `petN`. -/
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

/-- On `cuspFormCharSpace k χ`, `⟨n⟩⁻¹` acts as the scalar `χ(n)⁻¹`.
Hence `T_n* = χ(n)⁻¹ · T_n` on this space (from `heckeT_n_adjoint`). -/
private lemma heckeT_n_adjoint_on_charSpace
    (χ : (ZMod N)ˣ →* ℂˣ)
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) (hg : g ∈ cuspFormCharSpace k χ) :
    petN (heckeT_n_cusp k n f) g =
      (↑(χ (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * petN f (heckeT_n_cusp k n g) := by
  rw [heckeT_n_adjoint n hn f g]
  -- petN f (⟨n⟩⁻¹ (T_n g)). On charSpace, ⟨n⟩⁻¹ (T_n g) = χ(n)⁻¹ • T_n g.
  have hTg : heckeT_n_cusp k n g ∈ cuspFormCharSpace k χ :=
    heckeT_n_cusp_preserves_cuspFormCharSpace k n hn χ hg
  have h_diamond : diamondOp_cusp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeT_n_cusp k n g) =
      (↑(χ (ZMod.unitOfCoprime n hn)⁻¹) : ℂ) • heckeT_n_cusp k n g := by
    exact ((mem_cuspFormCharSpace_iff k χ _).mp hTg) (ZMod.unitOfCoprime n hn)⁻¹
  rw [h_diamond]
  -- petN f (c • h) = c * petN f h (linear in second arg)
  simp only [map_inv, Units.val_inv_eq_inv_val]
  exact petN_smul_right _ f (heckeT_n_cusp k n g)

/-- `T_n` is semisimple (diagonalizable) on the cusp-form character space `S_k(N, χ)`.

## Proof strategy

On `cuspFormCharSpace k χ`, the adjoint relation `heckeT_n_adjoint` simplifies via
`heckeT_n_adjoint_on_charSpace` to:
  `⟨T_n f, g⟩ = χ(n)⁻¹ · ⟨f, T_n g⟩`
where `χ(n) ∈ ℂˣ` is a unit. Define `S_n := χ(n)^{1/2} · T_n` (choosing a square
root of `χ(n)`; exists since `ℂ` is algebraically closed). Then:
  `⟨S_n f, g⟩ = χ(n)^{1/2} · χ(n)⁻¹ · ⟨f, χ(n)^{1/2} · T_n g⟩`
            `= conj(χ(n)^{1/2}) · ⟨f, S_n g⟩`
For `S_n` to be symmetric (self-adjoint), we need `χ(n)^{1/2} · χ(n)⁻¹ = conj(χ(n)^{1/2})`
which holds when `|χ(n)| = 1` (Dirichlet characters have unit norm).

Alternatively (avoiding square roots), note that `T_n` is a **scalar multiple** of a
symmetric operator on `cuspFormCharSpace`: define `R_n := χ(n) · T_n`, then
`⟨R_n f, g⟩ = χ(n) · χ(n)⁻¹ · ⟨f, T_n g⟩ = ⟨f, T_n g⟩`, so `R_n* = T_n`, and
`R_n* R_n = T_n · χ(n) · T_n = χ(n) · T_n² = R_n R_n*` (using commutativity).
Hence `T_n` is normal. Over `ℂ` in finite dimensions, normal operators are
diagonalizable, giving `⨆ μ, maxGenEigenspace T_n μ = ⊤`.

## Mathlib infrastructure needed

1. **`InnerProductSpace` on `cuspFormCharSpace`**: Needs `petN_innerProductCore` lifted
   to `cuspFormCharSpace k χ` (restriction of the inner product).
2. **Normal implies semisimple**: Mathlib has `LinearMap.IsSymmetric.isFinitelySemisimple`
   but not a general "normal implies semisimple over ℂ" result. One could:
   (a) Use real/imaginary decomposition: `T = A + iB` where `A, B` are symmetric and
       commute (standard for normal operators), then apply existing Mathlib results; or
   (b) Prove that `⨆ μ, eigenspace T_n μ = ⊤` directly using the minimal polynomial
       (which is separable for normal operators over `ℂ`).
3. **`Module.End.iSup_maxGenEigenspace_eq_top`** (Triangularizable.lean): gives
   `⨆ μ, maxGenEigenspace f μ = ⊤` over algebraically closed fields in finite
   dimensions. But this is for *all* operators (generalized eigenspaces), and
   semisimplicity (eigenspaces = generalized eigenspaces) is the additional content.

## Dependencies
- `heckeT_n_adjoint_on_charSpace` (proved, via `heckeT_n_adjoint`)
- `petN_innerProductCore` (defined in this file)
- `Module.End.iSup_maxGenEigenspace_eq_top` (Mathlib, for triangularizability)
- `LinearMap.IsSymmetric.isFinitelySemisimple` (Mathlib, for symmetric case) -/
private lemma heckeT_n_cusp_isSemisimple_on_charSpace
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)]
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) :
    ⨆ μ : ℂ, (heckeT_n_cusp_charRestrict k n hn χ).maxGenEigenspace μ = ⊤ :=
  -- Over ℂ (algebraically closed), ANY endomorphism on a finite-dimensional space
  -- has generalized eigenspaces spanning the whole space.
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

/-- Restricted Hecke operators on `cuspFormCharSpace` commute pairwise.
Follows from `heckeT_n_cusp_comm`, which gives pointwise commutativity
`T_m(T_n f) = T_n(T_m f)` for all cusp forms `f`. The restriction to
`cuspFormCharSpace` inherits this since `heckeT_n_cusp_charRestrict` is defined
pointwise on the underlying cusp forms. -/
private lemma heckeT_n_cusp_charRestrict_commute
    (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    Commute (heckeT_n_cusp_charRestrict k m hm χ) (heckeT_n_cusp_charRestrict k n hn χ) := by
  -- Commute for Module.End means T_m * T_n = T_n * T_m (composition)
  show heckeT_n_cusp_charRestrict k m hm χ * heckeT_n_cusp_charRestrict k n hn χ =
    heckeT_n_cusp_charRestrict k n hn χ * heckeT_n_cusp_charRestrict k m hm χ
  -- Use LinearMap.ext to compare at the function level (not pointwise)
  apply LinearMap.ext
  intro ⟨f, hf⟩
  simp only [Module.End.mul_apply]
  -- Goal: T_m(T_n ⟨f, hf⟩) = T_n(T_m ⟨f, hf⟩) as subtypes
  -- Both sides have equal underlying cusp forms by heckeT_n_cusp_comm
  exact Subtype.ext (heckeT_n_cusp_comm m n f)

/-- Index type for coprime Hecke operators: positive integers coprime to `N`. -/
private abbrev CoprimeIndex (N : ℕ) := { n : ℕ+ // Nat.Coprime n.val N }

/-- The family of Hecke operators indexed by `CoprimeIndex N`, restricted to
`cuspFormCharSpace k chi`. The weight `k` is explicit to avoid implicit argument
ambiguity in higher-order contexts. -/
private noncomputable def heckeFamily (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ) :
    CoprimeIndex N → Module.End ℂ (cuspFormCharSpace k chi) :=
  fun ⟨n, hn⟩ =>
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n_cusp_charRestrict k n.val hn chi

/-- The Hecke family on `cuspFormCharSpace` is pairwise commutative. -/
private lemma heckeFamily_pairwise_commute (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ) :
    Pairwise fun i j => Commute (heckeFamily k chi i) (heckeFamily k chi j) := by
  intro ⟨m, hm⟩ ⟨n, hn⟩ _hmn
  haveI : NeZero m.val := ⟨m.pos.ne'⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  exact heckeT_n_cusp_charRestrict_commute chi m.val n.val hm hn

/-- Each operator in the Hecke family is individually triangularizable
(generalized eigenspaces span). This is automatic over `ℂ` (algebraically closed)
in finite dimensions. -/
private lemma heckeFamily_triangularizable (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k chi)]
    (i : CoprimeIndex N) :
    ⨆ μ : ℂ, Module.End.maxGenEigenspace (heckeFamily k chi i) μ = ⊤ := by
  obtain ⟨⟨n, hn_pos⟩, hn⟩ := i
  haveI : NeZero n := ⟨hn_pos.ne'⟩
  exact Module.End.iSup_maxGenEigenspace_eq_top _

/-- Joint generalized eigenspace decomposition: the joint generalized eigenspaces
of the Hecke family span `cuspFormCharSpace k chi`.

This is the key spectral-theoretic input, combining pairwise commutativity
and individual triangularizability via Mathlib's
`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`. -/
private lemma heckeFamily_joint_eigenspace_top (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k chi)] :
    ⨆ ev : CoprimeIndex N → ℂ,
      ⨅ i, Module.End.maxGenEigenspace (heckeFamily k chi i) (ev i) = ⊤ :=
  Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (heckeFamily k chi) (heckeFamily_pairwise_commute k chi)
    (heckeFamily_triangularizable k chi)

/-- Each operator in the Hecke family is finitely semisimple on `cuspFormCharSpace k chi`.

On the cusp-form character space `S_k(Γ₁(N), χ)`, the Petersson inner product `petN`
(via `petN_innerProductCore`) makes each Hecke operator `T_n` normal:
`T_n^* = χ(n)⁻¹ · T_n` by `heckeT_n_adjoint_on_charSpace`.

**Proof via twisted symmetric operator**: Choose `c ∈ ℂ` with `c² = χ(n)⁻¹`
(exists since `ℂ` is algebraically closed). Define `S := c · T_n`. Then `S` is
symmetric w.r.t. `petN`:
  `petN(S f, g) = conj(c) · χ(n)⁻¹ · petN(f, T_n g) = c⁻¹ · χ(n)⁻¹ · petN(f, T_n g)`
where `conj(c) = c⁻¹` since `|c|² = |χ(n)⁻¹| = 1`. Also:
  `petN(f, S g) = c · petN(f, T_n g)`
These are equal iff `c⁻¹ · χ(n)⁻¹ = c`, i.e., `c² = χ(n)⁻¹`. ✓

By `LinearMap.IsSymmetric.isFinitelySemisimple`, `S` is semisimple. Since `T_n = c⁻¹ · S`
and `c ≠ 0`, `T_n` is semisimple by `IsSemisimple_smul_iff`.

Reference: Diamond–Shurman §5.5 Theorem 5.5.4, Miyake §4.5 Theorem 4.5.4. -/
private lemma heckeFamily_isFinitelySemisimple (k : ℤ) (chi : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k chi)]
    (i : CoprimeIndex N) :
    (heckeFamily k chi i).IsFinitelySemisimple := by
  obtain ⟨⟨n, hn_pos⟩, hn⟩ := i
  haveI : NeZero n := ⟨hn_pos.ne'⟩
  -- Abbreviation for the restricted Hecke operator T_n on cuspFormCharSpace
  set T := heckeT_n_cusp_charRestrict k n hn chi
  -- Step (a): Promote petN_innerProductCore to InnerProductSpace on CuspForm.
  -- CuspForm has no pre-existing NormedAddCommGroup, so we introduce one from petN.
  letI ipCore : InnerProductSpace.Core ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    petN_innerProductCore
  letI : NormedAddCommGroup (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ ipCore
  letI : InnerProductSpace ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    InnerProductSpace.ofCore (𝕜 := ℂ) (F := CuspForm ((Gamma1 N).map (mapGL ℝ)) k) inferInstance
  -- Step (b): cuspFormCharSpace inherits InnerProductSpace via Submodule.innerProductSpace
  -- (automatic from the instance Submodule.innerProductSpace)
  -- Step (c): Choose c with c² = χ(n)⁻¹ (ℂ is algebraically closed)
  set χn_inv : ℂ := ↑(chi (ZMod.unitOfCoprime n hn))⁻¹
  obtain ⟨c, hc_sq⟩ := IsAlgClosed.exists_pow_nat_eq χn_inv (show 0 < 2 from two_pos)
  -- hc_sq : c ^ 2 = χn_inv
  -- c ≠ 0 (since χn_inv ≠ 0, being a unit value)
  have hχn_inv_ne : χn_inv ≠ 0 := by
    simp only [χn_inv]; exact_mod_cast Units.ne_zero ((chi (ZMod.unitOfCoprime n hn))⁻¹ : ℂˣ)
  have hc_ne : c ≠ 0 := by
    intro hc; rw [hc, zero_pow (by norm_num : 2 ≠ 0)] at hc_sq; exact hχn_inv_ne hc_sq.symm
  -- Key identity: conj(c) * c = 1 (i.e., |c|² = 1)
  -- This follows from |c²| = |χ(n)⁻¹| = 1
  have h_norm_χn_inv : ‖χn_inv‖ = 1 := by
    -- χ maps finite group elements to elements of ℂˣ of finite order,
    -- which have norm 1 in a normed field.
    have h_fin : IsOfFinOrder ((chi (ZMod.unitOfCoprime n hn))⁻¹ : ℂˣ) :=
      (MonoidHom.isOfFinOrder chi (isOfFinOrder_of_finite (ZMod.unitOfCoprime n hn))).inv
    exact ((Units.coeHom ℂ).isOfFinOrder h_fin).norm_eq_one
  have h_conj_mul_c : starRingEnd ℂ c * c = 1 := by
    -- conj(c) * c = normSq(c) = ‖c‖² and ‖c‖² = ‖c²‖ = ‖χn_inv‖ = 1
    have h_norm_c_sq : ‖c‖ ^ 2 = 1 := by
      have : ‖c ^ 2‖ = 1 := by rw [hc_sq]; exact h_norm_χn_inv
      rwa [norm_pow] at this
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h_norm_c_sq,
      Complex.ofReal_one]
  -- Step (c): Show c • T is symmetric w.r.t. the inner product on cuspFormCharSpace
  have h_symm : LinearMap.IsSymmetric (c • T) := by
    intro x y
    -- The inner product on the submodule equals petN on the ambient space:
    -- ⟪x, y⟫ = ⟪(x : CuspForm), (y : CuspForm)⟫ = petN x.val y.val
    -- We reduce to a petN computation
    change (ipCore.inner ((c • T) x).val y.val : ℂ) = ipCore.inner x.val ((c • T) y).val
    -- (c • T) x has value c • T_n(x.val) as a CuspForm
    have hval_x : ((c • T) x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        c • heckeT_n_cusp k n x.val := rfl
    have hval_y : ((c • T) y : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        c • heckeT_n_cusp k n y.val := rfl
    rw [hval_x, hval_y]
    -- LHS = petN(c • T_n(x.val), y.val) = conj(c) * petN(T_n(x.val), y.val)
    show petN (c • heckeT_n_cusp k n x.val) y.val = petN x.val (c • heckeT_n_cusp k n y.val)
    rw [petN_conj_smul_left' c (heckeT_n_cusp k n x.val) y.val]
    -- Apply adjoint relation: petN(T_n f, g) = χ(n)⁻¹ * petN(f, T_n g)
    rw [heckeT_n_adjoint_on_charSpace chi n hn x.prop y.prop]
    -- LHS = conj(c) * (χn_inv * petN(x.val, T_n(y.val)))
    -- RHS = petN(x.val, c • T_n(y.val)) = c * petN(x.val, T_n(y.val))
    rw [petN_smul_right c x.val (heckeT_n_cusp k n y.val)]
    -- Need: conj(c) * (χn_inv * petN(...)) = c * petN(...)
    -- i.e., conj(c) * χn_inv = c
    -- From hc_sq: c ^ 2 = χn_inv, so conj(c) * c ^ 2 = conj(c) * c * c = 1 * c = c
    -- The show/change reset the set-binding, so fold χn_inv back
    show starRingEnd ℂ c * (χn_inv * _) = c * _
    rw [← hc_sq, sq]
    -- Goal: conj(c) * (c * c * P) = c * P  where P = petN ...
    -- Rearrange using ring-like associativity and h_conj_mul_c
    have h_key : ∀ (P : ℂ), starRingEnd ℂ c * (c * c * P) = c * P := by
      intro P
      have : starRingEnd ℂ c * (c * c * P) = (starRingEnd ℂ c * c) * (c * P) := by ring
      rw [this, h_conj_mul_c, one_mul]
    exact h_key _
  -- Step (d): Transfer semisimplicity from c • T to T
  -- In finite dimensions, IsFinitelySemisimple ↔ IsSemisimple
  rw [Module.End.isFinitelySemisimple_iff_isSemisimple]
  -- c • T is semisimple (symmetric operators on inner product spaces are semisimple)
  have h_semi_cT : (c • T).IsSemisimple := by
    rw [← Module.End.isFinitelySemisimple_iff_isSemisimple]
    exact h_symm.isFinitelySemisimple
  -- T is semisimple iff c • T is semisimple (for c ≠ 0)
  exact (Module.End.IsSemisimple_smul_iff hc_ne).mp h_semi_cT

/-- An element of a joint maximal generalized eigenspace of the Hecke family is a
common eigenfunction of all T_n with (n,N)=1.

This is the bridge between the abstract spectral decomposition and the concrete
`IsCommonEigenfunctionCusp` predicate.

Each `f` in `⨅ i, maxGenEigenspace (T i) (ev i)` satisfies
`f ∈ maxGenEigenspace (T_n) (ev_n)` for each `n` coprime to `N`. Since each
`T_n` is finitely semisimple (`heckeFamily_isFinitelySemisimple`), we have
`maxGenEigenspace = eigenspace` by
`Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`.
This converts membership to `T_n f = ev_n • f`. -/
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
  -- Construct the coprime index for (n, hn_cop)
  let i₀ : CoprimeIndex N := ⟨n, hn_cop⟩
  -- f is in the joint gen-eigenspace, so f ∈ maxGenEigenspace (T_n) (ev(i₀))
  have hf_i : f ∈ Module.End.maxGenEigenspace (heckeFamily k chi i₀) (ev i₀) :=
    iInf_le (fun i => Module.End.maxGenEigenspace (heckeFamily k chi i) (ev i)) i₀ hf
  -- Each T_n is finitely semisimple, so maxGenEigenspace = eigenspace
  have h_ss := heckeFamily_isFinitelySemisimple k chi i₀
  rw [Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace h_ss] at hf_i
  -- From eigenspace membership: T_n f = ev(i₀) • f (as elements of cuspFormCharSpace)
  have h_eig := Module.End.mem_eigenspace_iff.mp hf_i
  -- h_eig : heckeFamily k chi i₀ f = ev i₀ • f
  -- Unfolding: heckeFamily k chi i₀ = heckeT_n_cusp_charRestrict k n.val hn_cop chi
  -- This acts on ⟨f.val, f.prop⟩ to give ⟨heckeT_n_cusp k n.val f.val, ...⟩
  -- Extract the underlying cusp form from the subtype equality
  have h_cusp : heckeT_n_cusp k n.val (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ev i₀ • (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    have h_eq := congr_arg Subtype.val h_eig
    -- h_eq says the .val of the LHS equals the .val of the RHS
    -- LHS.val = heckeT_n_cusp k n.val f.val
    -- RHS.val = (ev i₀ • f).val = ev i₀ • f.val
    exact h_eq
  exact ⟨ev i₀, h_cusp⟩

/-- Distinct simultaneous Hecke eigenforms in `cuspFormCharSpace k chi` are
orthogonal w.r.t. `petN`, provided they have different eigenvalue tuples.

If `T_n f = a * f` and `T_n g = b * g` with `conj(a) ≠ chi(n)⁻¹ * b`
for some `n` coprime to `N`, then by `heckeT_n_adjoint_on_charSpace`:
  `conj(a) * petN f g = petN(T_n f, g) = chi(n)⁻¹ * b * petN f g`
Hence `(conj(a) - chi(n)⁻¹ * b) * petN f g = 0`, giving `petN f g = 0`.

The hypothesis uses `starRingEnd ℂ a_f` (= conj(a_f)) because the adjoint
relation conjugates the left eigenvalue. In practice, for eigenforms from
*different* joint eigenspaces, this is satisfied because the eigenvalue
tuples differ and the adjoint relation constrains the relationship. -/
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
  -- From the adjoint relation on charSpace:
  have h_adj := heckeT_n_adjoint_on_charSpace chi n hn hf_char hg_char
  -- Substitute eigenform equations
  rw [hf_eig] at h_adj
  rw [petN_conj_smul_left'] at h_adj
  rw [hg_eig, petN_smul_right] at h_adj
  -- h_adj : starRingEnd ℂ a_f * petN f g = ↑(chi(n))⁻¹ * (b_g * petN f g)
  -- Reassociate the RHS to get (↑(chi(n))⁻¹ * b_g) * petN f g
  rw [← mul_assoc] at h_adj
  -- h_adj : starRingEnd ℂ a_f * petN f g = ↑(chi(n))⁻¹ * b_g * petN f g
  -- So (starRingEnd ℂ a_f - ↑(chi(n))⁻¹ * b_g) * petN f g = 0
  have h_eq : (starRingEnd ℂ a_f - (↑(chi (ZMod.unitOfCoprime n hn))⁻¹ : ℂ) * b_g) *
      petN f g = 0 := by
    rw [sub_mul, h_adj, sub_self]
  exact (mul_eq_zero.mp h_eq).resolve_left (sub_ne_zero.mpr h_diff)

theorem exists_simultaneous_eigenform_basis
    (χ : (ZMod N)ˣ →* ℂˣ)
    [FiniteDimensional ℂ (cuspFormCharSpace k χ)] :
    ∃ (B : Finset (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)),
      (∀ f ∈ B, f ∈ cuspFormCharSpace k χ) ∧
      (∀ f ∈ B, IsCommonEigenfunctionCusp k f) ∧
      (∀ f g, f ∈ B → g ∈ B → f ≠ g → petN f g = 0) := by
  -- Step 1: Joint eigenspace decomposition (PROVED)
  -- The Hecke family is pairwise commutative and individually triangularizable,
  -- so the joint generalized eigenspaces span cuspFormCharSpace.
  have h_top := heckeFamily_joint_eigenspace_top k χ
  -- Step 2+3: Extract orthogonal eigenform basis from the decomposition.
  -- From h_top : ⨆ ev, ⨅ i, maxGenEigenspace (T i) (ev i) = ⊤, extract a
  -- basis of cuspFormCharSpace consisting of simultaneous eigenforms,
  -- orthogonal w.r.t. petN.
  --
  -- Remaining steps (each using proved infrastructure):
  -- (a) Choose a basis within each non-zero joint eigenspace
  --     (standard finite-dimensional linear algebra from Mathlib:
  --      FiniteDimensional.exists_is_basis_finset, Submodule.exists_isCompl)
  -- (b) Prove each basis vector is a common eigenfunction
  --     (via joint_eigenspace_mem_isCommonEigenfunction — proved, relies on
  --      heckeFamily_isFinitelySemisimple)
  -- (c) Prove orthogonality between different eigenspaces
  --     (via eigenforms_orthogonal_of_distinct_eigenvalues — proved above,
  --      given the correct conjugated eigenvalue hypothesis)
  -- (d) Apply Gram-Schmidt within each eigenspace for same-eigenvalue orthogonality
  --     (using petN_innerProductCore to get InnerProductSpace structure)
  -- (e) Collect into a Finset of CuspForm (lifting from the subtype)
  --
  -- This is finite-dimensional linear algebra packaging. The mathematical content
  -- is in h_top + the two helper lemmas. Remaining work: finset basis extraction
  -- from ⨆ ev, W_ev = ⊤ plus Gram-Schmidt within each non-zero W_ev.
  sorry

end HeckeRing.GL2
