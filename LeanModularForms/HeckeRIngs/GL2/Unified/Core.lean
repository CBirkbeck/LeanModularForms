 /-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeRingHomCharSpace_General

/-!
# Unified good-Hecke-family interface

This file isolates the "away from the level" Hecke structure that the current
project already has on character spaces: endomorphisms indexed by positive
integers coprime to `N`, together with the three core laws

* `T_1 = 1`
* `T_{mn} = T_m T_n` for `Nat.Coprime m n`
* pairwise commutativity

The point of this interface is to give a common API for experimental unification
work without forcing the full twisted double-coset refactor into the active
SMO path.
-/

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2.Unified

variable {N : ℕ} [NeZero N]

/-- Indices for the good Hecke operators: positive integers coprime to `N`. -/
abbrev GoodIndex (N : ℕ) := HeckeRing.GL2.coprimeToN N

/-- A "good Hecke family" on a complex vector space, indexed by positive naturals
coprime to the level `N`. This is the common algebraic interface currently used
downstream in the `Γ₁(N), χ` theory. -/
structure GoodHeckeFamily (N : ℕ) [NeZero N] (V : Type*)
    [AddCommGroup V] [Module ℂ V] where
  op : GoodIndex N → Module.End ℂ V
  map_one' : op 1 = 1
  map_mul_of_coprime' : ∀ m n : GoodIndex N, Nat.Coprime (m : ℕ) (n : ℕ) →
      op (m * n) = op m * op n
  commute' : ∀ m n : GoodIndex N, Commute (op m) (op n)

namespace GoodHeckeFamily

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

@[simp] lemma map_one (F : GoodHeckeFamily N V) : F.op 1 = 1 :=
  F.map_one'

lemma map_mul_of_coprime (F : GoodHeckeFamily N V)
    (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) :
    F.op (m * n) = F.op m * F.op n :=
  F.map_mul_of_coprime' m n hmn

lemma commute (F : GoodHeckeFamily N V) (m n : GoodIndex N) :
    Commute (F.op m) (F.op n) :=
  F.commute' m n

lemma pairwise_commute (F : GoodHeckeFamily N V) :
    Pairwise fun m n : GoodIndex N => Commute (F.op m) (F.op n) := by
  intro m n _
  exact F.commute m n

/-- Pointwise commutativity extracted from `Commute` at the `Module.End` level. -/
lemma commute_apply (F : GoodHeckeFamily N V) (m n : GoodIndex N) (v : V) :
    F.op m (F.op n v) = F.op n (F.op m v) := by
  exact LinearMap.congr_fun (F.commute m n).eq v

/-- Coprime multiplicativity already forces commutativity on coprime indices.
This is the ring-theoretic route used in the experimental layer when the proof
source is `T_{mn} = T_m T_n`, rather than an independently packaged
commutativity theorem. -/
lemma commute_of_coprime_from_mul (F : GoodHeckeFamily N V)
    (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) :
    Commute (F.op m) (F.op n) := by
  show F.op m * F.op n = F.op n * F.op m
  calc
    F.op m * F.op n = F.op (m * n) := by
      symm
      exact F.map_mul_of_coprime m n hmn
    _ = F.op (n * m) := by
      congr 1
      exact Subtype.ext (Nat.mul_comm (m : ℕ) (n : ℕ))
    _ = F.op n * F.op m := by
      exact F.map_mul_of_coprime n m hmn.symm

/-- Pointwise form of `commute_of_coprime_from_mul`. -/
lemma commute_apply_of_coprime_from_mul (F : GoodHeckeFamily N V)
    (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) (v : V) :
    F.op m (F.op n v) = F.op n (F.op m v) := by
  exact LinearMap.congr_fun (F.commute_of_coprime_from_mul m n hmn).eq v

/-- Conjugate an endomorphism along a linear equivalence. -/
noncomputable def conjEnd (e : V ≃ₗ[ℂ] W) (T : Module.End ℂ V) :
    Module.End ℂ W :=
  e.toLinearMap ∘ₗ T ∘ₗ e.symm.toLinearMap

@[simp] lemma conjEnd_apply (e : V ≃ₗ[ℂ] W) (T : Module.End ℂ V) (w : W) :
    conjEnd e T w = e (T (e.symm w)) := rfl

@[simp] lemma conjEnd_one (e : V ≃ₗ[ℂ] W) :
    conjEnd e (1 : Module.End ℂ V) = 1 := by
  ext w
  simp [conjEnd]

@[simp] lemma conjEnd_mul (e : V ≃ₗ[ℂ] W) (T S : Module.End ℂ V) :
    conjEnd e (T * S) = conjEnd e T * conjEnd e S := by
  ext w
  simp [conjEnd, Module.End.mul_apply]

/-- Transport a good Hecke family across a linear equivalence. -/
  noncomputable def transport (e : V ≃ₗ[ℂ] W) (F : GoodHeckeFamily N V) :
    GoodHeckeFamily N W where
  op n := conjEnd e (F.op n)
  map_one' := by
    rw [F.map_one]
    exact conjEnd_one e
  map_mul_of_coprime' m n hmn := by
    show conjEnd e (F.op (m * n)) = conjEnd e (F.op m) * conjEnd e (F.op n)
    rw [F.map_mul_of_coprime m n hmn, conjEnd_mul]
  commute' m n := by
    show conjEnd e (F.op m) * conjEnd e (F.op n) =
      conjEnd e (F.op n) * conjEnd e (F.op m)
    rw [← conjEnd_mul, ← conjEnd_mul, (F.commute m n).eq]

@[simp] lemma transport_apply (e : V ≃ₗ[ℂ] W) (F : GoodHeckeFamily N V)
    (n : GoodIndex N) (w : W) :
    (transport e F).op n w = e (F.op n (e.symm w)) := rfl

end GoodHeckeFamily

end HeckeRing.GL2.Unified
