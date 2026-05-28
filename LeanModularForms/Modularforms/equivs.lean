/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
public import Mathlib.Tactic

@[expose] public section

/-!
# Auxiliary equivalences

A handful of `Equiv`s on `ℤ` and on `Fin 2 → α` that are convenient for index manipulation in
`tsum`/`Summable` reindexing arguments.
-/

open TopologicalSpace Set Metric Filter Function Complex

/-- Negation as an `Equiv` on `ℤ`. -/
def negEquiv : ℤ ≃ ℤ where
  toFun n := -n
  invFun n := -n
  left_inv := neg_neg
  right_inv := neg_neg

/-- Successor as an `Equiv` on `ℤ`. -/
def succEquiv : ℤ ≃ ℤ where
  toFun n := n.succ
  invFun n := n.pred
  left_inv := Int.pred_succ
  right_inv := Int.succ_pred

/-- Swap the two components of a function `Fin 2 → α`. -/
def swap {α : Type*} : (Fin 2 → α) → (Fin 2 → α) := fun x ↦ ![x 1, x 0]

@[simp]
lemma swap_apply {α : Type*} (b : Fin 2 → α) : swap b = ![b 1, b 0] := rfl

lemma swap_involutive {α : Type*} (b : Fin 2 → α) : swap (swap b) = b := by
  ext i; fin_cases i <;> rfl

/-- The swap-of-`Fin 2` map as an `Equiv`. -/
def swap_equiv {α : Type*} : Equiv (Fin 2 → α) (Fin 2 → α) :=
  ⟨swap, swap, swap_involutive, swap_involutive⟩
