/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.DeltaBSystem

/-!
# Hecke adjoint theory: DS double-coset tile bridge.

Fourth module of the split of `AdjointTheoryPetersson`. Covers the T024 DS
double-coset tile bridge interface (`DSDoubleCosetTileBridge`) and the
branch/blocker sum-chain reductions.
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

/-! ### T024 DS double-coset tile bridge interface -/

open UpperHalfPlane ModularGroup MeasureTheory in
def DSDoubleCosetTileBridge
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
theorem petN_heckeT_p_adjoint_standard_form_of_doubleCosetTileBridge
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
theorem petN_heckeT_p_symmetric_form_of_doubleCosetTileBridge
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

/-! ### Named Prop bundles for recurring sum/equality patterns.

The branch sum chains (M_∞ and T_p upper) reuse a small number of long
expressions across many theorems. Bundling them as `Prop`s shrinks the
signatures from 30-100 lines down to a few lines each. Each named Prop is
`rfl`-equal to its inline form, so any value of the bundled type doubles as a
proof of the original expression (and vice versa). -/

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The M_∞-branch *tile-shift-to-prefactored* equation: sum-over-`q` of a
`M_∞-shifted-tile` peterssonInner on `⟨d⟩⁻¹f` and `(⟨d⟩⁻¹g ∣[T_p_upper 0]) ∣[ε]`
equals sum-over-`q` of `peterssonInner fd (f ∣[(q.out)⁻¹]) (g ∣[M_∞ * σ⟨ε⟩(q).out⁻¹])`.
Used as both the conclusion of `h_M_infty_tile_shift_to_prefactored_*` and the
hypothesis of `M_infty_branch_sum_slash_adjoint_reindex_prefactored` etc. -/
def MInftyTileShiftPrefactored
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The T_p-upper-branch *tile-shift-to-prefactored* equation: sum-over-`(q,b)` of
a `T_p_upper(b)-shifted-tile` peterssonInner on `⟨d⟩⁻¹f` and
`(⟨d⟩⁻¹g ∣[T_p_upper 0]) ∣[ε]` equals sum-over-`(q,b)` of
`peterssonInner fd (f ∣[(q.out)⁻¹]) (g ∣[T_p_upper(b) * σ⟨ε⟩(q).out⁻¹])`. -/
def TpUpperTileShiftPrefactored
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The M_∞-branch *FD-slash-exchange* equation: sum-over-`q` of
`peterssonInner fd (f ∣[T_p_lower · γ₀ · (q.out)⁻¹]) (g ∣[σ⟨ε⟩(q).out⁻¹])`
equals sum-over-`q` of `peterssonInner fd (f ∣[(q.out)⁻¹]) (g ∣[M_∞ · σ⟨ε⟩(q).out⁻¹])`.
Used as hypothesis of `h_M_infty_tile_shift_to_prefactored_of_FD_slash_exchange`. -/
def MInftyFDSlashExchange
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The T_p-upper-branch *FD-slash-exchange* equation, double sum over `(q,b)`. -/
def TpUpperFDSlashExchange
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The M_∞-branch *balanced* equation (hypothesis of
`petN_LHS_dist_eq_RHS_absorbed_from_branches`): sum-over-`q` of
`peterssonInner fd (f ∣[T_p_lower · γ₀·M_∞ · (q.out)⁻¹]) (g ∣[ε · (q.out)⁻¹])`
equals the σ-shifted form. -/
def MInftyBranchBalanced
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The T_p-upper-branch *balanced* equation, double sum over `(q,b)`. -/
def TpUpperBranchBalanced
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The T_p_upper(b)-shifted-tile *SL-tile balance* equation. -/
def TpUpperBSLTileBalance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
      (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The M_∞-shifted-tile *SL-tile balance* equation: peterssonInner on the
`M_∞ · (q.out)⁻¹`-tile union, with `(⟨d⟩⁻¹f) ∣[M_∞]` slot 2 swapped to
`⟨d⟩f ∣[M_∞]` on the right and the diamond moved from `f` to `g`. -/
def MInftySLTileBalance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
      (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The pairwise-AE-disjoint hypothesis for the `M_∞`-shifted-tile union. -/
def MInftyTilePairwiseAEDisjoint
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) : Prop :=
  Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
      (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
      (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The null-measurability hypothesis for each `M_∞`-shifted-tile piece. -/
def MInftyTileNullMeasurable
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) : Prop :=
  ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
    NullMeasurableSet
      (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The LHS-side integrability hypothesis for the `M_∞`-shifted-tile union. -/
def MInftyIntegrableLHS
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  IntegrableOn
    (fun τ ↦ petersson k
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
        peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The RHS-side integrability hypothesis for the `M_∞`-shifted-tile union. -/
def MInftyIntegrableRHS
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  IntegrableOn
    (fun τ ↦ petersson k
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
        peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
      ⇑g τ)
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp

/-! #### α-parameterized variants (used in the inner `h_α_…` family) -/

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The pairwise-AE-disjoint hypothesis for the `α`-shifted-tile union. -/
def AlphaTilePairwiseAEDisjoint (α : GL (Fin 2) ℝ) : Prop :=
  Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
      ((α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
      ((α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The null-measurability hypothesis for each `α`-shifted-tile piece. -/
def AlphaTileNullMeasurable (α : GL (Fin 2) ℝ) : Prop :=
  ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
    NullMeasurableSet
      ((α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The LHS-side integrability hypothesis for the `α`-shifted-tile union. -/
def AlphaIntegrableLHS
    (p : ℕ) (hpN : Nat.Coprime p N) (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  IntegrableOn
    (fun τ ↦ petersson k
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
        peterssonAdj α) τ)
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The RHS-side integrability hypothesis for the `α`-shifted-tile union. -/
def AlphaIntegrableRHS
    (p : ℕ) (hpN : Nat.Coprime p N) (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  IntegrableOn
    (fun τ ↦ petersson k
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
        peterssonAdj α) ⇑g τ)
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The `α-FD balance` equation: aggregate-tile peterssonInner on the
`α · (q.out)⁻¹`-tile union, with the diamond moved from the f-slot to the
α-adjoint-slashed g-slot. -/
def AlphaFDBalance
    (p : ℕ) (hpN : Nat.Coprime p N) (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
      peterssonAdj α) ⇑g

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The `α-post-swap balance` equation: same as `AlphaFDBalance` but with
the integration domain transformed by `peterssonAdj α`. -/
def AlphaPostSwapBalance
    (p : ℕ) (hpN : Nat.Coprime p N) (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
    (⇑g ∣[k] α)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The α-SL-tile balance equation: aggregate `peterssonInner` over the
plain SL-tile union (no α factor), with the diamond shifted from f's slot to
the α-slashed g-slot. -/
def AlphaSLTileBalance
    (p : ℕ) (hpN : Nat.Coprime p N) (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
      (⇑g ∣[k] α)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The α-balanced form: per-q `peterssonInner` summed where the diamond is
on the LHS f-slot via `α · (q.out)⁻¹`, equals the symmetric form with the
diamond on the f-slot only. -/
def AlphaBalanced
    (p : ℕ) (hpN : Nat.Coprime p N) (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The α-canonical form: balanced equation after reindexing via the σ-quotient
equivalence; i.e., g is slashed by `σ⟨ε⟩(q).out⁻¹`. -/
def AlphaCanonical
    (p : ℕ) (hpN : Nat.Coprime p N) (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The α-`T_p_lower`-form FD-slash-exchange equation, abstract over α and a
factorisation matrix γ_α. Specialises to `MInftyFDSlashExchange` when α is M_∞
and γ_α is the M_∞-specific gamma factor. -/
def AlphaTpLowerFDSlashExchange
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (γ_α : SL(2, ℤ))
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
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
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
lemma petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex
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

/-- `⟨d⟩⁻¹ ∘ ⟨d⟩` is the identity on cusp forms. -/
private lemma diamondOp_cusp_inv_diamondOp_cusp (u : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k u⁻¹ (diamondOp_cusp k u f) = f := by
  show diamondOpCusp k u⁻¹ (diamondOpCusp k u f) = f
  rw [← LinearMap.comp_apply, ← diamondOpCusp_mul, inv_mul_cancel, diamondOpCusp_one,
    LinearMap.id_apply]

/-- `⟨d⟩ ∘ ⟨d⟩⁻¹` is the identity on cusp forms. -/
private lemma diamondOp_cusp_diamondOp_cusp_inv (u : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k u (diamondOp_cusp k u⁻¹ f) = f := by
  show diamondOpCusp k u (diamondOpCusp k u⁻¹ f) = f
  rw [← LinearMap.comp_apply, ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one,
    LinearMap.id_apply]

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
  rw [diamondOp_cusp_inv_diamondOp_cusp]

open UpperHalfPlane ModularGroup MeasureTheory in
lemma slash_M_infty_eq_diamond_slash_T_p_lower_factor
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
  rw [diamondOp_cusp_inv_diamondOp_cusp (ZMod.unitOfCoprime p hpN) g] at h
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
lemma slash_T_p_upper_eq_diamond_slash_T_p_lower_factor
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
  rw [diamondOp_cusp_inv_diamondOp_cusp (ZMod.unitOfCoprime p hpN) g] at h
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
  rw [diamondOp_cusp_diamondOp_cusp_inv (ZMod.unitOfCoprime p hpN) f] at h
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
    rw [diamondOp_cusp_diamondOp_cusp_inv (ZMod.unitOfCoprime p hpN) g] at h
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
  rw [diamondOp_cusp_diamondOp_cusp_inv (ZMod.unitOfCoprime p hpN) f] at h
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
    rw [diamondOp_cusp_diamondOp_cusp_inv (ZMod.unitOfCoprime p hpN) g] at h
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
lemma sum_peterssonInner_LHS_M_infty_to_tile_form
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
lemma sum_peterssonInner_LHS_upper_to_tile_form
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
lemma sum_peterssonInner_M_infty_tile_form_collapse
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

theorem glMap_T_p_upper_det_pos (p : ℕ) (hp : 0 < p) (b : ℕ) :
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
/-- Conjugate orientation of `peterssonInner_slash_adjoint_coset`: pushes the
adjoint of `β` onto the **left** (`f`) slot.  Shared tail of the per-`q` RHS
tile-form lemmas for both the `M_∞` and `T_p` upper branches. -/
private lemma peterssonInner_slash_adjoint_q_summand_left
    (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val) (q : SL(2, ℤ)) (f g : ℍ → ℂ) :
    peterssonInner k fd
        (f ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ))
        (g ∣[k] (β * (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ))) =
      peterssonInner k (β • ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)))
        (f ∣[k] peterssonAdj β) g := by
  rw [← peterssonInner_conj_symm k fd, peterssonInner_slash_adjoint_coset β hβ q g f]
  exact peterssonInner_conj_symm k _ _ _

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
  rw [← slash_M_infty_eq_diamond_slash_T_p_lower_factor p hp hpN g q,
    peterssonInner_slash_adjoint_q_summand_left _
      (glMap_M_infty_det_pos N p hp.pos hpN) q (⇑f) (⇑g),
    slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_upper_zero_slash_gamma0 p hp hpN f]

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
  rw [← slash_T_p_upper_eq_diamond_slash_T_p_lower_factor p hp hpN b g q,
    peterssonInner_slash_adjoint_q_summand_left _
      (glMap_T_p_upper_det_pos p hp.pos b) q (⇑f) (⇑g),
    slash_peterssonAdj_T_p_upper_eq_slash_T_p_upper_zero_slash_gamma0 p hp hpN b f]

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
/-- The σ-reindex step for the `M_∞` RHS branch: starting from the adjoint-form
sum (the `f ∣ adj⁻¹` summands over the `σ`-shifted cosets), reindex along
`Gamma1QuotEquivOfGamma0` and rewrite each `f ∣ adj⁻¹ ∣ q.out⁻¹` slot to a
diamond, landing on the tile form. -/
private lemma sum_peterssonInner_RHS_M_infty_adjoint_form_sigma_reindex_to_tile_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
lemma sum_peterssonInner_RHS_M_infty_to_tile_form_via_sigma
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
  exact sum_peterssonInner_RHS_M_infty_adjoint_form_sigma_reindex_to_tile_form p hp hpN f g

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The σ-reindex step for the `T_p` upper RHS branch (per `b`): the analogue of
`sum_peterssonInner_RHS_M_infty_adjoint_form_sigma_reindex_to_tile_form` with the
`M_∞` slot replaced by `T_p_upper p b`. -/
private lemma sum_peterssonInner_RHS_upper_adjoint_form_sigma_reindex_to_tile_form_per_b
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
lemma sum_peterssonInner_RHS_upper_to_tile_form_via_sigma_per_b
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
  exact sum_peterssonInner_RHS_upper_adjoint_form_sigma_reindex_to_tile_form_per_b
    p hp hpN b f g

open UpperHalfPlane ModularGroup MeasureTheory in
lemma sum_peterssonInner_upper_tile_form_swap
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
lemma sum_peterssonInner_upper_tile_form_per_b_collapse
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
lemma petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex_absorbed
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

theorem petN_heckeT_p_adjoint_standard_form_of_LHS_bridge
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
theorem M_infty_branch_sum_slash_adjoint_reindex_prefactored
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_tile_shift_to_prefactored : MInftyTileShiftPrefactored p hp hpN f g) :
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
theorem M_infty_branch_hypothesis_via_sum_chain
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_tile_shift_to_prefactored : MInftyTileShiftPrefactored p hp hpN f g) :
    MInftyBranchBalanced p hp hpN f g := by
  show _ = _
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
theorem T_p_upper_branch_sum_slash_adjoint_reindex_prefactored
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_upper_tile_shift_to_prefactored : TpUpperTileShiftPrefactored p hp hpN f g) :
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
theorem T_p_upper_branch_hypothesis_via_sum_chain
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_upper_tile_shift_to_prefactored : TpUpperTileShiftPrefactored p hp hpN f g) :
    TpUpperBranchBalanced p hp hpN f g := by
  show _ = _
  rw [T_p_upper_branch_sum_slash_adjoint_reindex_prefactored p hp hpN f g
    h_upper_tile_shift_to_prefactored,
    ← T_p_upper_branch_RHS_unfactor_slot2 p hp hpN f g]

open UpperHalfPlane ModularGroup MeasureTheory in
theorem petN_LHS_dist_eq_RHS_absorbed_from_branches
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M_infty_branch : MInftyBranchBalanced p hp hpN f g)
    (h_upper_branch : TpUpperBranchBalanced p hp hpN f g) :
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
theorem h_M_infty_tile_shift_to_prefactored_of_FD_slash_exchange
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_FD_slash_exchange : MInftyFDSlashExchange p hp hpN f g) :
    MInftyTileShiftPrefactored p hp hpN f g := by
  show _ = _
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
theorem h_upper_tile_shift_to_prefactored_of_FD_slash_exchange
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_FD_slash_exchange : TpUpperFDSlashExchange p hp hpN f g) :
    TpUpperTileShiftPrefactored p hp hpN f g := by
  show _ = _
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
theorem h_α_FD_slash_exchange_T_p_lower_form_of_canonical
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (γ_α : SL(2, ℤ))
    (h_factor : ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) * α =
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* _) γ_α : GL (Fin 2) ℝ))
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_canonical_α : AlphaCanonical p hpN α f g) :
    AlphaTpLowerFDSlashExchange p hp hpN α γ_α f g := by
  show _ = _
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
/-- LHS rewrite for `h_α_canonical_form_of_balanced`: in each `g`-argument,
slashing by the `σ`-shifted coset representative equals applying `⟨d⟩⁻¹` to `g`
first (the summed form of `slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv_GL`). -/
private lemma sum_peterssonInner_diamond_inv_g_slot_eq_g_slash_sigma
    (p : ℕ) (hpN : Nat.Coprime p N) (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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

open UpperHalfPlane ModularGroup MeasureTheory in
/-- RHS rewrite for `h_α_canonical_form_of_balanced`: reindex the `diamond f`/`g`
sum along `σ = Gamma1QuotEquivOfGamma0`, then cancel the `⟨d⟩⁻¹⟨d⟩` on `f`,
landing on the bare-`f`/`σ`-shifted-`g` form. -/
private lemma sum_peterssonInner_diamond_f_slot_sigma_reindex_to_g_α_form
    (p : ℕ) (hpN : Nat.Coprime p N) (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
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
  exact congrArg _ (diamondOp_cusp_inv_diamondOp_cusp (ZMod.unitOfCoprime p hpN) f)

open UpperHalfPlane ModularGroup MeasureTheory in
theorem h_α_canonical_form_of_balanced
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_balanced : AlphaBalanced p hpN α f g) :
    AlphaCanonical p hpN α f g := by
  show _ = _
  rw [sum_peterssonInner_diamond_inv_g_slot_eq_g_slash_sigma p hpN α f g, h_balanced,
    sum_peterssonInner_diamond_f_slot_sigma_reindex_to_g_α_form p hpN α f g]

open UpperHalfPlane ModularGroup MeasureTheory in
theorem balanced_α_of_aggregate_FD_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : AlphaTilePairwiseAEDisjoint (N := N) α)
    (hm : AlphaTileNullMeasurable (N := N) α)
    (hint_LHS : AlphaIntegrableLHS p hpN α f g)
    (hint_RHS : AlphaIntegrableRHS p hpN α f g)
    (h_FD_balance : AlphaFDBalance p hpN α f g) :
    AlphaBalanced p hpN α f g := by
  show _ = _
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
theorem h_FD_balance_of_post_swap_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_post_swap_balance : AlphaPostSwapBalance p hpN α f g) :
    AlphaFDBalance p hpN α f g := by
  show _ = _
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
theorem h_post_swap_balance_of_SL_tile_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_SL_tile_balance : AlphaSLTileBalance p hpN α f g) :
    AlphaPostSwapBalance p hpN α f g := by
  show _ = _
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
  have h_cancel : diamondOp_cusp k d (diamondOp_cusp k d⁻¹ G) = G :=
    diamondOp_cusp_diamondOp_cusp_inv d G
  calc petN (diamondOp_cusp k d F) G
      = petN (diamondOp_cusp k d F) (diamondOp_cusp k d
          (diamondOp_cusp k d⁻¹ G)) := by rw [h_cancel]
    _ = petN F (diamondOp_cusp k d⁻¹ G) :=
        diamondOp_petersson_unitary d F (diamondOp_cusp k d⁻¹ G)

open UpperHalfPlane ModularGroup MeasureTheory in
theorem h_M_infty_SL_tile_balance_iff_T_p_lower_diamond_form
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
theorem h_T_p_upper_SL_tile_balance_iff_T_p_lower_diamond_form
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
    TpUpperBSLTileBalance p hp hpN b f g :=
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
def TpUpperZeroShiftedFormBlocker
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
private theorem h_M_infty_SL_tile_balance_of_T_p_upper_zero_shifted_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_shifted : TpUpperZeroShiftedFormBlocker p hp hpN f g) :
    MInftySLTileBalance p hp hpN f g :=
  (h_M_infty_SL_tile_balance_iff_T_p_upper_zero_shifted_form p hp hpN f g).mpr
    h_shifted

open UpperHalfPlane ModularGroup MeasureTheory in
def TpUpperBranchDiamondFormBlocker
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
theorem h_T_p_upper_SL_tile_balance_from_blocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : TpUpperBranchDiamondFormBlocker p hp hpN b f g) :
    TpUpperBSLTileBalance p hp hpN b f g :=
  h_T_p_upper_SL_tile_balance_of_T_p_lower_diamond_form p hp hpN b f g h

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_M_infty_SL_tile_balance_from_blocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : TpUpperZeroShiftedFormBlocker p hp hpN f g) :
    MInftySLTileBalance p hp hpN f g :=
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
    (hd : MInftyTilePairwiseAEDisjoint p hp hpN)
    (hm : MInftyTileNullMeasurable p hp hpN)
    (hint_LHS : MInftyIntegrableLHS p hp hpN f g)
    (hint_RHS : MInftyIntegrableRHS p hp hpN f g)
    (h_M_infty_SL_tile_balance : MInftySLTileBalance p hp hpN f g) :
    MInftyTileShiftPrefactored p hp hpN f g :=
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
theorem h_M_infty_tile_shift_to_prefactored_from_blocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : MInftyTilePairwiseAEDisjoint p hp hpN)
    (hm : MInftyTileNullMeasurable p hp hpN)
    (hint_LHS : MInftyIntegrableLHS p hp hpN f g)
    (hint_RHS : MInftyIntegrableRHS p hp hpN f g)
    (h_blocker : TpUpperZeroShiftedFormBlocker p hp hpN f g) :
    MInftyTileShiftPrefactored p hp hpN f g :=
  h_M_infty_tile_shift_to_prefactored_from_SL_tile_balance p hp hpN f g
    hd hm hint_LHS hint_RHS
    (h_M_infty_SL_tile_balance_from_blocker p hp hpN f g h_blocker)

open UpperHalfPlane ModularGroup MeasureTheory in
theorem h_M_infty_FD_slash_exchange_from_SL_tile_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : MInftyTilePairwiseAEDisjoint p hp hpN)
    (hm : MInftyTileNullMeasurable p hp hpN)
    (hint_LHS : MInftyIntegrableLHS p hp hpN f g)
    (hint_RHS : MInftyIntegrableRHS p hp hpN f g)
    (h_M_infty_SL_tile_balance : MInftySLTileBalance p hp hpN f g) :
    MInftyFDSlashExchange p hp hpN f g :=
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

end HeckeRing.GL2
