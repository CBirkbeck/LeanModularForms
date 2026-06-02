/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Newforms
import LeanModularForms.Modularforms.Delta
import LeanModularForms.Modularforms.JacobiTheta

/-!
# The discriminant Δ is a Hecke eigenform

This file proves that the modular discriminant `Delta : CuspForm Γ(1) 12` is a Hecke
eigenform: for every `n : ℕ+`, the operator `T_n` acts on `Delta` as a scalar. The
argument is a dimension count: `dim S_12(Γ₁(1)) = 1` and `Delta ≠ 0`, so every cusp
form in `S_12(Γ₁(1))` is a scalar multiple of `Delta`. We bridge `Γ(1)` and `Γ₁(1)` via
the equality `Gamma 1 = Gamma1 1 = ⊤`.

## Main results

* `Delta_lvl1` — the discriminant viewed as a `CuspForm ((Gamma1 1).map (mapGL ℝ)) 12`
* `Delta_lvl1_ne_zero` — `Delta_lvl1 ≠ 0`
* `finrank_cuspForm_lvl1_weight12` — `dim S_12(Γ₁(1)) = 1`
* `Delta_lvl1_isEigenform` — `IsEigenform Delta_lvl1`
-/

namespace HeckeRing.GL2

open scoped MatrixGroups CongruenceSubgroup
open ModularForm UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup

private lemma Gamma1_one_top : Gamma1 (1 : ℕ) = ⊤ := by
  ext γ
  simp only [Gamma1_mem, Subgroup.mem_top, iff_true]
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

private lemma Gamma_one_eq_Gamma1_one : Gamma (1 : ℕ) = Gamma1 (1 : ℕ) := by
  rw [Gamma_one_top, Gamma1_one_top]

private lemma map_Gamma_one_eq_map_Gamma1_one :
    (Gamma (1 : ℕ)).map (mapGL ℝ) = (Gamma1 (1 : ℕ)).map (mapGL ℝ) :=
  Gamma_one_eq_Gamma1_one ▸ rfl

/-- The discriminant `Delta` viewed as a cusp form for `(Gamma1 1).map (mapGL ℝ)`. -/
noncomputable def Delta_lvl1 : CuspForm ((Gamma1 (1 : ℕ)).map (mapGL ℝ)) 12 where
  toFun := Delta
  slash_action_eq' γ hγ :=
    Delta.slash_action_eq' γ (map_Gamma_one_eq_map_Gamma1_one ▸ hγ)
  holo' := Delta.holo'
  zero_at_cusps' {_} hc := Delta.zero_at_cusps' (map_Gamma_one_eq_map_Gamma1_one ▸ hc)

@[simp]
lemma Delta_lvl1_apply (z : ℍ) : Delta_lvl1 z = Δ z := Delta_apply z

lemma Delta_lvl1_ne_zero : Delta_lvl1 ≠ 0 := fun h ↦
  Δ_ne_zero UpperHalfPlane.I <| by simpa using DFunLike.congr_fun h UpperHalfPlane.I

/-- A linear equivalence between cusp forms over `(Gamma 1).map (mapGL ℝ)` and over
`(Gamma1 1).map (mapGL ℝ)`: the underlying function is the same; only the invariance
group changes (but it is the same group). -/
private noncomputable def cuspForm_Gamma_one_equiv_Gamma1_one (k : ℤ) :
    CuspForm ((Gamma (1 : ℕ)).map (mapGL ℝ)) k ≃ₗ[ℂ]
    CuspForm ((Gamma1 (1 : ℕ)).map (mapGL ℝ)) k where
  toFun f :=
    { toFun := f, holo' := f.holo'
      slash_action_eq' γ hγ := f.slash_action_eq' γ (map_Gamma_one_eq_map_Gamma1_one ▸ hγ)
      zero_at_cusps' {_} hc := f.zero_at_cusps' (map_Gamma_one_eq_map_Gamma1_one ▸ hc) }
  invFun f :=
    { toFun := f, holo' := f.holo'
      slash_action_eq' γ hγ := f.slash_action_eq' γ (map_Gamma_one_eq_map_Gamma1_one ▸ hγ)
      zero_at_cusps' {_} hc := f.zero_at_cusps' (map_Gamma_one_eq_map_Gamma1_one ▸ hc) }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The dimension of `S_12(Γ₁(1))` is 1. -/
lemma finrank_cuspForm_lvl1_weight12 :
    Module.finrank ℂ (CuspForm ((Gamma1 (1 : ℕ)).map (mapGL ℝ)) 12) = 1 := by
  rw [← LinearEquiv.finrank_eq (cuspForm_Gamma_one_equiv_Gamma1_one 12)]
  apply Module.finrank_eq_of_rank_eq
  rw [LinearEquiv.rank_eq (CuspForms_iso_Modforms 12)]
  simpa using ModularForm.levelOne_weight_zero_rank_one

/-- **The discriminant `Delta` is a Hecke eigenform**: for every `n : ℕ+`, the Hecke
operator `T_n` maps `Delta` to a scalar multiple of `Delta`. The proof is a dimension
argument: `dim S_12(Γ₁(1)) = 1` and `Delta ≠ 0`, so every cusp form in `S_12(Γ₁(1))` is
a scalar multiple of `Delta`. -/
theorem Delta_lvl1_isEigenform : IsEigenform (N := 1) (k := 12) Delta_lvl1 := by
  classical
  have h : ∀ n : ℕ+, ∃ c : ℂ, c • Delta_lvl1 = heckeT_n_cusp 12 n.val Delta_lvl1 := fun n ↦ by
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    exact (finrank_eq_one_iff_of_nonzero' Delta_lvl1 Delta_lvl1_ne_zero).mp
      finrank_cuspForm_lvl1_weight12 (heckeT_n_cusp 12 n.val Delta_lvl1)
  exact ⟨fun n ↦ (h n).choose, fun n _ ↦ (h n).choose_spec.symm⟩

end HeckeRing.GL2
