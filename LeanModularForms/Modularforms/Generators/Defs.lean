module

public import LeanModularForms.Modularforms.DimensionFormulas
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Generators of the graded ring of level 1 modular forms: Definitions

This file defines the weight function `E₄E₆Weight`, the evaluation homomorphism
`evalE₄E₆ : ℂ[X₀, X₁] →ₐ[ℂ] ⨁ k, M_k(Γ(1))`, and the polynomial `Delta_poly`,
along with basic API lemmas (evaluation on generators, odd-weight vanishing,
monomial weight existence, and `Δ ∈ range evalE₄E₆`).
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

/-- Weight function assigning weight 4 to E₄ (variable 0) and weight 6 to E₆ (variable 1). -/
def E₄E₆Weight : Fin 2 → ℕ := ![4, 6]

/-- Evaluation homomorphism sending `ℂ[X₀, X₁]` to the graded ring of level 1 modular forms
via `X₀ ↦ E₄` and `X₁ ↦ E₆`. -/
noncomputable def evalE₄E₆ :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ]
      DirectSum ℤ (fun k => ModularForm (CongruenceSubgroup.Gamma 1) k) :=
  MvPolynomial.aeval
    ![DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄,
      DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆]

/-- The polynomial `Δ_poly = (1/1728)(X₀³ - X₁²)` in `ℂ[X₀, X₁]`,
mapping to `Δ` under `evalE₄E₆`. -/
noncomputable def Delta_poly : MvPolynomial (Fin 2) ℂ :=
  (1 / 1728 : ℂ) • (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)

/-! ## Odd-weight vanishing -/

/-- For odd weight k, every modular form of weight k for Γ(1) is zero. -/
theorem levelOne_odd_weight_eq_zero {k : ℤ} (hk : Odd k)
    (f : ModularForm (CongruenceSubgroup.Gamma 1) k) : f = 0 := by
  ext z
  have hmod : (f.toFun ∣[k] (-1 : SL(2, ℤ))) z = f z :=
    congrFun (f.slash_action_eq' _
      (Subgroup.mem_map_of_mem _ (CongruenceSubgroup.mem_Gamma_one (-1)))) z
  rw [SL_slash_apply] at hmod
  rw [ModularGroup.SL_neg_smul, one_smul] at hmod
  have hdenom : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) (-1 : SL(2, ℤ)))) ↑z = -1 := by
    rw [ModularGroup.denom_apply]
    simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, ne_eq, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, neg_zero, Int.cast_zero, zero_mul, Matrix.one_apply_eq, Int.reduceNeg,
      Int.cast_neg, Int.cast_one, zero_add]
  rw [hdenom, zpow_neg, hk.neg_one_zpow, inv_neg, inv_one] at hmod
  simp only [SlashInvariantForm.toFun_eq_coe, ModularForm.toSlashInvariantForm_coe] at hmod
  simp only [ModularForm.zero_apply]
  exact (mul_eq_zero.mp (show 2 * f z = 0 by linear_combination -hmod)).resolve_left two_ne_zero

/-- For odd weight k, the space of modular forms of weight k for Γ(1) has rank zero. -/
theorem levelOne_odd_weight_rank_zero {k : ℤ} (hk : Odd k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = 0 := by
  rw [rank_zero_iff_forall_zero]
  exact levelOne_odd_weight_eq_zero hk

/-! ## Combinatorial helpers for monomial weight decomposition -/

/-- For even k ≥ 4, there exist a, b ∈ ℕ with 4a + 6b = k. -/
lemma monomial_weight_exists (k : ℕ) (hk : 4 ≤ k) (hkeven : Even k) :
    ∃ a b : ℕ, 4 * a + 6 * b = k := by
  obtain ⟨m, rfl⟩ := hkeven
  rcases Nat.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact ⟨n, 0, by omega⟩
  · exact ⟨n - 1, 1, by omega⟩

/-! ## Q-expansion helpers -/

/-- The 0th q-expansion coefficient of E_k raised to the n-th power equals 1. -/
lemma Ek_q_exp_zero_pow (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (n : ℕ) :
    (qExpansion 1 (E k hk)).coeff 0 ^ n = 1 := by
  rw [Ek_q_exp_zero k hk hk2]
  exact one_pow n

/-! ## Delta in the range of evalE₄E₆ -/

/-- Key computation: `evalE₄E₆ (X 0) = DirectSum.of _ 4 E₄`. -/
lemma evalE₄E₆_X0 :
    evalE₄E₆ (MvPolynomial.X 0) =
      DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄ := by
  simp only [evalE₄E₆, MvPolynomial.aeval_X, Matrix.cons_val_zero]

/-- Key computation: `evalE₄E₆ (X 1) = DirectSum.of _ 6 E₆`. -/
lemma evalE₄E₆_X1 :
    evalE₄E₆ (MvPolynomial.X 1) =
      DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆ := by
  simp only [evalE₄E₆, Fin.isValue, MvPolynomial.aeval_X, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

/-- `evalE₄E₆ (C c) = algebraMap ℂ _ c`. -/
lemma evalE₄E₆_C (c : ℂ) :
    evalE₄E₆ (MvPolynomial.C c) =
      algebraMap ℂ (DirectSum ℤ (fun k => ModularForm Γ(1) k)) c :=
  MvPolynomial.aeval_C _ c

/-- The evaluation of `Delta_poly` under `evalE₄E₆`. -/
lemma evalE₄E₆_Delta_poly :
    evalE₄E₆ Delta_poly =
      (1 / 1728 : ℂ) •
        ((DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄) ^ 3 -
         (DirectSum.of (fun k : ℤ =>
            ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆) ^ 2) := by
  simp only [Delta_poly, map_smul, map_sub, map_pow, evalE₄E₆_X0, evalE₄E₆_X1]

/-- The discriminant `Δ` lies in the range of `evalE₄E₆`. -/
lemma delta_mem_range_evalE₄E₆ :
    DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 12
      (ModForm_mk (CongruenceSubgroup.Gamma 1) 12 Delta) ∈ Set.range evalE₄E₆ := by
  refine ⟨Delta_poly, ?_⟩
  rw [evalE₄E₆_Delta_poly]
  ext i
  by_cases hi : i = 12
  · subst hi
    simp only [DirectSum.smul_apply, DirectSum.sub_apply, DirectSum.of_eq_same]
    rw [show ModForm_mk Γ(1) 12 Delta = ModForm_mk Γ(1) 12 Delta_E4_E6_aux from by
      rw [Delta_E4_eqn], Delta_E4_E6_eq]
    simp only [DirectSum.sub_apply]
  · simp only [DirectSum.smul_apply, DirectSum.sub_apply, DirectSum.of_eq_of_ne _ _ _ hi]
    have he4 : ((DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄)
        ^ 3) i = 0 := by
      rw [pow_three, DirectSum.of_mul_of, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_ne _ _ _ (by omega)
    have he6 : ((DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆)
        ^ 2) i = 0 := by
      rw [pow_two, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_ne _ _ _ (by omega)
    rw [he4, he6, sub_self, smul_zero]
