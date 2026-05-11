/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Commensurable
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Prototype: Hecke Ring via Quotient of Δ (Option 2)

We construct the Hecke ring as `Finsupp (HeckeCoset P) ℤ` where `HeckeCoset P`
is the quotient of `P.Δ` by the double coset equivalence `g ~ h ↔ HgH = HhH`.

No `∃` in any structure. No `.choose` anywhere. Representatives via `Quotient.out`.
-/

open scoped Pointwise
open DoubleCoset

namespace HeckeRing.V2

variable {G : Type*} [Group G]

-- ═══════════════════════════════════════════════════════════
-- 1. HECKE PAIR
-- ═══════════════════════════════════════════════════════════

/-- A Hecke pair: subgroup `H` and submonoid `Δ` with `H ≤ Δ ≤ commensurator(H)`. -/
structure HeckePair (G : Type*) [Group G] where
  H : Subgroup G
  Δ : Submonoid G
  h_le : H.toSubmonoid ≤ Δ
  h_comm : Δ ≤ (Subgroup.Commensurable.commensurator H).toSubmonoid

variable (P : HeckePair G)

-- ═══════════════════════════════════════════════════════════
-- 2. HECKE COSET (Quotient of Δ)
-- ═══════════════════════════════════════════════════════════

/-- Two elements of `Δ` define the same double coset. -/
def dcRel (g h : P.Δ) : Prop :=
  doubleCoset (g : G) P.H P.H = doubleCoset (h : G) P.H P.H

instance dcSetoid : Setoid P.Δ where
  r := dcRel P
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- A Hecke double coset: equivalence class of `Δ`-elements under `HgH = HhH`. -/
def HeckeCoset := Quotient (dcSetoid P)

noncomputable instance : DecidableEq (HeckeCoset P) := Classical.decEq _

namespace HeckeCoset

/-- The identity double coset. -/
def one : HeckeCoset P := ⟦⟨1, P.Δ.one_mem⟩⟧

/-- The underlying set `HgH`, well-defined on the quotient. -/
noncomputable def toSet : HeckeCoset P → Set G :=
  Quotient.lift (fun (g : P.Δ) => doubleCoset (g : G) P.H P.H)
    (fun _ _ (h : dcRel P _ _) => h)

/-- A representative `g : Δ` (via `Quotient.out`). -/
noncomputable def rep (D : HeckeCoset P) : P.Δ := Quotient.out D

/-- `⟦g⟧ = ⟦h⟧ ↔ HgH = HhH`. -/
lemma eq_iff (g h : P.Δ) : (⟦g⟧ : HeckeCoset P) = ⟦h⟧ ↔
    doubleCoset (g : G) P.H P.H = doubleCoset (h : G) P.H P.H :=
  Quotient.eq (r := dcSetoid P)

/-- The representative lies in its double coset. -/
@[simp] lemma toSet_mk (g : P.Δ) :
    toSet P (⟦g⟧ : HeckeCoset P) = doubleCoset (g : G) P.H P.H := rfl

lemma toSet_eq_rep (D : HeckeCoset P) :
    toSet P D = doubleCoset (rep P D : G) P.H P.H := by
  conv_lhs => rw [← Quotient.out_eq D]
  exact toSet_mk P (rep P D)

lemma rep_mem (D : HeckeCoset P) : (rep P D : G) ∈ toSet P D := by
  rw [toSet_eq_rep]
  exact mem_doubleCoset_self _ _ _

/-- Induction: suffices to prove for `⟦g⟧`, all `g : Δ`. -/
protected lemma ind {motive : HeckeCoset P → Prop}
    (h : ∀ g : P.Δ, motive ⟦g⟧) : ∀ D, motive D := Quotient.ind h

/-- Two-argument induction. -/
protected lemma ind₂ {motive : HeckeCoset P → HeckeCoset P → Prop}
    (h : ∀ g₁ g₂ : P.Δ, motive ⟦g₁⟧ ⟦g₂⟧) : ∀ D₁ D₂, motive D₁ D₂ := Quotient.ind₂ h

end HeckeCoset

-- ═══════════════════════════════════════════════════════════
-- 3. DECOMPOSITION QUOTIENT
-- ═══════════════════════════════════════════════════════════

/-- `H ∩ gHg⁻¹` as a subgroup of `H`. -/
def conjSub (g : P.Δ) : Subgroup P.H :=
  (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H

/-- The decomposition quotient `H / (H ∩ gHg⁻¹)`: indexes left cosets in `HgH`. -/
def decompQuot (g : P.Δ) := P.H ⧸ conjSub P g

/-- The decomposition quotient is finite (from the commensurator condition). -/
noncomputable instance instFintypeDecompQuot (g : P.Δ) : Fintype (decompQuot P g) := by
  apply Subgroup.fintypeOfIndexNeZero; sorry

/-- The degree: number of left cosets in `HgH`. -/
noncomputable def degree (g : P.Δ) : ℕ := Fintype.card (decompQuot P g)

lemma degree_pos (g : P.Δ) : 0 < degree P g := by
  haveI : Nonempty (decompQuot P g) := ⟨⟦1⟧⟩; exact Fintype.card_pos

-- ═══════════════════════════════════════════════════════════
-- 4. HECKE MULTIPLICITY
-- ═══════════════════════════════════════════════════════════

/-- The multiplication map: `(σᵢ, τⱼ) ↦ ⟦σᵢ g₁ τⱼ g₂⟧`. -/
noncomputable def mulMap (g₁ g₂ : P.Δ)
    (p : decompQuot P g₁ × decompQuot P g₂) : HeckeCoset P :=
  ⟦⟨(p.1.out : P.H) * g₁ * ((p.2.out : P.H) * g₂),
    P.Δ.mul_mem (P.Δ.mul_mem (P.h_le (p.1.out : P.H).2) g₁.2)
      (P.Δ.mul_mem (P.h_le (p.2.out : P.H).2) g₂.2)⟩⟧

/-- The support of the product: finitely many double cosets. -/
noncomputable def mulSupport (g₁ g₂ : P.Δ) : Finset (HeckeCoset P) :=
  Finset.image (mulMap P g₁ g₂) Finset.univ

/-- The Hecke multiplicity: `m(g₁, g₂; D) = #{(σᵢ, τⱼ) | σᵢ g₁ τⱼ g₂ ∈ D}`. -/
noncomputable def heckeMultiplicity (g₁ g₂ : P.Δ) (D : HeckeCoset P) : ℤ :=
  Nat.card {p : decompQuot P g₁ × decompQuot P g₂ | mulMap P g₁ g₂ p = D}

/-- Multiplicity is nonneg. -/
lemma heckeMultiplicity_nonneg (g₁ g₂ : P.Δ) (D : HeckeCoset P) :
    0 ≤ heckeMultiplicity P g₁ g₂ D := Nat.cast_nonneg' _

/-- Multiplicity is zero outside the support. -/
lemma heckeMultiplicity_eq_zero_of_nmem (g₁ g₂ : P.Δ) (D : HeckeCoset P)
    (hD : D ∉ mulSupport P g₁ g₂) : heckeMultiplicity P g₁ g₂ D = 0 := by
  simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero]
  left; rw [isEmpty_subtype]; intro p hp
  exact hD (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩)

/-- Multiplicity is nonzero on the support. -/
lemma heckeMultiplicity_ne_zero_of_mem (g₁ g₂ : P.Δ) (D : HeckeCoset P)
    (hD : D ∈ mulSupport P g₁ g₂) : heckeMultiplicity P g₁ g₂ D ≠ 0 := by
  simp only [heckeMultiplicity, ne_eq, Nat.cast_eq_zero, Nat.card_eq_zero, not_or,
    not_isEmpty_iff]
  simp only [mulSupport, Finset.mem_image, Finset.mem_univ, true_and] at hD
  obtain ⟨p, hp⟩ := hD
  exact ⟨⟨⟨p, hp⟩⟩, by exact not_infinite_iff_finite.mpr inferInstance⟩

-- ═══════════════════════════════════════════════════════════
-- 5. THE KEY THEOREM
-- ═══════════════════════════════════════════════════════════

/-- **Shimura Prop 3.4**: The multiplicity depends only on double coset classes. -/
theorem heckeMultiplicity_well_defined (g₁ g₁' g₂ g₂' : P.Δ)
    (h₁ : dcRel P g₁ g₁') (h₂ : dcRel P g₂ g₂') (D : HeckeCoset P) :
    heckeMultiplicity P g₁ g₂ D = heckeMultiplicity P g₁' g₂' D := by
  sorry

-- ═══════════════════════════════════════════════════════════
-- 6. HECKE RING
-- ═══════════════════════════════════════════════════════════

/-- The Hecke ring type: formal ℤ-linear combinations of double cosets. -/
abbrev HeckeAlg := Finsupp (HeckeCoset P) ℤ

/-- The multiplication coefficients as a Finsupp. -/
noncomputable def mCoeff (g₁ g₂ : P.Δ) : HeckeAlg P where
  support := mulSupport P g₁ g₂
  toFun := heckeMultiplicity P g₁ g₂
  mem_support_toFun D := by
    simp only [ne_eq, Finset.mem_coe]
    exact ⟨heckeMultiplicity_ne_zero_of_mem P g₁ g₂ D,
      fun h => by_contra fun hm => h (heckeMultiplicity_eq_zero_of_nmem P g₁ g₂ D hm)⟩

/-- Multiplication on the Hecke algebra. -/
noncomputable instance : Mul (HeckeAlg P) where
  mul f g := f.sum fun D₁ a₁ => g.sum fun D₂ a₂ =>
    a₁ • a₂ • mCoeff P D₁.rep D₂.rep

/-- The one element. -/
noncomputable instance : One (HeckeAlg P) where
  one := Finsupp.single (HeckeCoset.one P) 1

-- ═══════════════════════════════════════════════════════════
-- 7. RING PROPERTIES
-- ═══════════════════════════════════════════════════════════

theorem mul_one' (f : HeckeAlg P) : f * 1 = f := by sorry
theorem one_mul' (f : HeckeAlg P) : 1 * f = f := by sorry
theorem mul_assoc' (f g h : HeckeAlg P) : f * g * h = f * (g * h) := by sorry

/-- The Hecke algebra is a ring. -/
noncomputable instance : Ring (HeckeAlg P) where
  mul_assoc := mul_assoc' P
  one_mul := one_mul' P
  mul_one := mul_one' P
  left_distrib _ _ _ := by sorry
  right_distrib _ _ _ := by sorry
  zero_mul _ := by simp [HMul.hMul, Mul.mul, Finsupp.sum_zero_index]
  mul_zero _ := by simp [HMul.hMul, Mul.mul, Finsupp.sum_zero_index, Finsupp.sum_zero]
  natCast n := n • Finsupp.single (HeckeCoset.one P) 1
  intCast n := n • Finsupp.single (HeckeCoset.one P) 1
  natCast_zero := by simp
  natCast_succ n := by
    change (n + 1) • Finsupp.single (HeckeCoset.one P) 1 =
      n • Finsupp.single (HeckeCoset.one P) 1 + Finsupp.single (HeckeCoset.one P) 1
    rw [add_smul, one_smul]
  intCast_negSucc n := by
    change (Int.negSucc n) • Finsupp.single (HeckeCoset.one P) 1 =
      -((n + 1 : ℕ) • Finsupp.single (HeckeCoset.one P) 1)
    show ((Int.negSucc n : ℤ) • _ : HeckeAlg P) = _
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl, neg_smul, natCast_zsmul]
  __ := inferInstanceAs (AddCommGroup (HeckeAlg P))

-- ═══════════════════════════════════════════════════════════
-- 8. COMMUTATIVITY VIA ANTI-INVOLUTION
-- ═══════════════════════════════════════════════════════════

/-- An anti-involution of a Hecke pair. -/
structure AntiInvolution where
  toFun : G →* Gᵐᵒᵖ
  involutive : ∀ g, (toFun (toFun g).unop).unop = g
  map_H : ∀ g ∈ P.H, (toFun g).unop ∈ P.H
  map_Δ : ∀ g ∈ P.Δ, (toFun g).unop ∈ P.Δ

variable {P}

/-- The anti-involution acts on `Δ`. -/
def AntiInvolution.onΔ (ι : AntiInvolution P) (g : P.Δ) : P.Δ :=
  ⟨(ι.toFun g).unop, ι.map_Δ g g.2⟩

/-- The anti-involution respects the double coset equivalence. -/
lemma AntiInvolution.onΔ_dcRel (ι : AntiInvolution P) {g h : P.Δ} (hgh : dcRel P g h) :
    dcRel P (ι.onΔ g) (ι.onΔ h) := by sorry

/-- The induced map on `HeckeCoset`. -/
noncomputable def AntiInvolution.onCoset (ι : AntiInvolution P) :
    HeckeCoset P → HeckeCoset P :=
  Quotient.lift (fun g => (⟦ι.onΔ g⟧ : HeckeCoset P))
    (fun _ _ h => (HeckeCoset.eq_iff P _ _).mpr (ι.onΔ_dcRel h))

/-- `onCoset` is involutive. -/
lemma AntiInvolution.onCoset_invol (ι : AntiInvolution P) :
    Function.Involutive ι.onCoset :=
  HeckeCoset.ind P fun g => by
    simp only [AntiInvolution.onCoset, Quotient.lift_mk]
    rw [HeckeCoset.eq_iff]
    change doubleCoset ((ι.toFun ((ι.toFun g).unop)).unop : G) _ _ = doubleCoset (g : G) _ _
    rw [ι.involutive g]

/-- **Shimura Prop 3.8**: If `ι` fixes all double cosets, the Hecke ring is commutative. -/
theorem commutative_of_fixed_antiInvolution (ι : AntiInvolution P)
    (h_fix : ∀ D : HeckeCoset P, ι.onCoset D = D) :
    ∀ f g : HeckeAlg P, f * g = g * f := by sorry

/-- CommRing instance from a fixed-point anti-involution. -/
noncomputable def instCommRing (ι : AntiInvolution P)
    (h_fix : ∀ D : HeckeCoset P, ι.onCoset D = D) : CommRing (HeckeAlg P) :=
  { inferInstanceAs (Ring (HeckeAlg P)) with
    mul_comm := commutative_of_fixed_antiInvolution ι h_fix }

end HeckeRing.V2
