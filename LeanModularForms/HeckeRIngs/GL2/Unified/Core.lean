/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeRingHomCharSpace_General

/-!
# Good Hecke families

This file packages the "away from the level" Hecke structure on a complex vector
space: endomorphisms indexed by positive integers coprime to `N`, together with
the three core laws `T_1 = 1`, `T_{mn} = T_m T_n` for coprime `m, n`, and
pairwise commutativity.

## Main definitions

* `GoodHeckeFamily`: a family of commuting endomorphisms indexed by
  `GoodIndex N` (positive naturals coprime to `N`), multiplicative on coprime
  indices.
* `GoodHeckeFamily.transport`: transport of a good Hecke family across a linear
  equivalence.
-/

namespace HeckeRing.GL2.Unified

variable {N : ℕ} [NeZero N]

/-- Indices for the good Hecke operators: positive integers coprime to `N`. -/
abbrev GoodIndex (N : ℕ) := HeckeRing.GL2.coprimeToN N

/-- A "good Hecke family" on a complex vector space: endomorphisms indexed by
positive naturals coprime to the level `N`, commuting pairwise and multiplicative
on coprime indices. -/
@[ext]
structure GoodHeckeFamily (N : ℕ) [NeZero N] (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- The endomorphism `T_n` attached to a coprime-to-`N` index `n`. -/
  op : GoodIndex N → Module.End ℂ V
  /-- `T_1` is the identity. -/
  map_one' : op 1 = 1
  /-- `T_{m * n} = T_m * T_n` whenever `m` and `n` are coprime. -/
  map_mul_of_coprime' : ∀ m n : GoodIndex N, Nat.Coprime (m : ℕ) (n : ℕ) → op (m * n) = op m * op n
  /-- The endomorphisms `T_m` and `T_n` commute. -/
  commute' : ∀ m n : GoodIndex N, Commute (op m) (op n)

namespace GoodHeckeFamily

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A good Hecke family maps the index `1` to the identity endomorphism. -/
@[simp] lemma map_one (F : GoodHeckeFamily N V) : F.op 1 = 1 := F.map_one'

/-- The operator `F.op` is multiplicative on coprime pairs of indices. -/
lemma map_mul_of_coprime (F : GoodHeckeFamily N V) (m n : GoodIndex N)
    (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) : F.op (m * n) = F.op m * F.op n :=
  F.map_mul_of_coprime' m n hmn

/-- The operators of a good Hecke family pairwise commute. -/
lemma commute (F : GoodHeckeFamily N V) (m n : GoodIndex N) : Commute (F.op m) (F.op n) :=
  F.commute' m n

/-- Transport a good Hecke family across a linear equivalence. -/
def transport (e : V ≃ₗ[ℂ] W) (F : GoodHeckeFamily N V) : GoodHeckeFamily N W where
  op n := e.conjRingEquiv (F.op n)
  map_one' := by simp
  map_mul_of_coprime' m n hmn := by simp [F.map_mul_of_coprime m n hmn]
  commute' m n := (F.commute m n).map e.conjRingEquiv

/-- The operator of a transported family acts by conjugating with the equivalence. -/
lemma transport_apply (e : V ≃ₗ[ℂ] W) (F : GoodHeckeFamily N V) (n : GoodIndex N) (w : W) :
    (transport e F).op n w = e (F.op n (e.symm w)) := rfl

/-- The operator of a transported family, as conjugation by the equivalence. -/
@[simp] lemma transport_op (e : V ≃ₗ[ℂ] W) (F : GoodHeckeFamily N V) (n : GoodIndex N) :
    (transport e F).op n = e.conjRingEquiv (F.op n) := rfl

end GoodHeckeFamily

end HeckeRing.GL2.Unified
