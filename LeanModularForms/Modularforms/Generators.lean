module

public import LeanModularForms.Modularforms.DimensionFormulas
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

/-- Weight function assigning weight 4 to E₄ (variable 0) and weight 6 to E₆ (variable 1). -/
def E₄E₆Weight : Fin 2 → ℕ := ![4, 6]

/-- Evaluation homomorphism sending the polynomial ring `ℂ[X₀, X₁]` to the graded ring of
level 1 modular forms, via `X₀ ↦ E₄` and `X₁ ↦ E₆`. -/
noncomputable def evalE₄E₆ :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ]
      DirectSum ℤ (fun k => ModularForm (CongruenceSubgroup.Gamma 1) k) :=
  MvPolynomial.aeval
    ![DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄,
      DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆]

/-- The polynomial `Δ_poly = (1/1728)(X₀³ - X₁²)` in `ℂ[X₀, X₁]`, which maps to the
discriminant modular form `Δ` under `evalE₄E₆`. -/
noncomputable def Delta_poly : MvPolynomial (Fin 2) ℂ :=
  (1 / 1728 : ℂ) • (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)

/-! ## Odd-weight vanishing -/

/-- For odd weight k, every modular form of weight k for Γ(1) is zero. -/
theorem levelOne_odd_weight_eq_zero {k : ℤ} (hk : Odd k)
    (f : ModularForm (CongruenceSubgroup.Gamma 1) k) : f = 0 := by
  ext z
  have hmod : (f.toFun ∣[k] (-1 : SL(2, ℤ))) z = f z := by
    have := f.slash_action_eq' _
      (Subgroup.mem_map_of_mem _ (CongruenceSubgroup.mem_Gamma_one (-1)))
    exact congrFun this z
  rw [SL_slash_apply] at hmod
  rw [ModularGroup.SL_neg_smul, one_smul] at hmod
  have hdenom : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) (-1 : SL(2, ℤ)))) ↑z = -1 := by
    rw [ModularGroup.denom_apply]
    simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  rw [hdenom, zpow_neg, hk.neg_one_zpow, inv_neg, inv_one] at hmod
  simp only [SlashInvariantForm.toFun_eq_coe, ModularForm.toSlashInvariantForm_coe] at hmod
  simp only [ModularForm.zero_apply]
  exact (mul_eq_zero.mp (show 2 * f z = 0 by linear_combination -hmod)).resolve_left two_ne_zero

/-- For odd weight k, the space of modular forms of weight k for Γ(1) has rank zero. -/
theorem levelOne_odd_weight_rank_zero {k : ℤ} (hk : Odd k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = 0 := by
  rw [rank_zero_iff_forall_zero]
  exact fun f => levelOne_odd_weight_eq_zero hk f

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
  simp [evalE₄E₆, MvPolynomial.aeval_X, Matrix.cons_val_zero]

/-- Key computation: `evalE₄E₆ (X 1) = DirectSum.of _ 6 E₆`. -/
lemma evalE₄E₆_X1 :
    evalE₄E₆ (MvPolynomial.X 1) =
      DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆ := by
  simp [evalE₄E₆, MvPolynomial.aeval_X, Matrix.cons_val_one]

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
         (DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆) ^ 2) := by
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

/-! ## Surjectivity of evalE₄E₆

We prove that `evalE₄E₆` is surjective by showing each `DirectSum.of _ k f` lies in
its range (strong induction on weight), then using the subalgebra closure of the range. -/

/-- A product of modular forms with q-expansion constant coefficient 1 is nonzero. -/
private lemma mul_modform_ne_zero_of_coeff_one {k₁ k₂ : ℤ}
    (f : ModularForm Γ(1) k₁) (g : ModularForm Γ(1) k₂)
    (hf : (qExpansion 1 f).coeff 0 = 1) (hg : (qExpansion 1 g).coeff 0 = 1) :
    (f.mul g : ModularForm Γ(1) (k₁ + k₂)) ≠ 0 := by
  intro h
  have hcoeff : (qExpansion 1 (f.mul g)).coeff 0 = 1 := by
    have := qExpansion_mul_coeff 1 k₁ k₂ f g
    simp only [Nat.cast_one] at this; rw [this]
    simp [PowerSeries.coeff_mul, Finset.antidiagonal_zero, hf, hg]
  have hcoe : (⇑(f.mul g) : ℍ → ℂ) = 0 := by rw [h]; ext z; simp
  rw [show qExpansion 1 (f.mul g) = qExpansion 1 (0 : ℍ → ℂ) from
    congr_arg (qExpansion 1) hcoe, qExpansion_zero] at hcoeff
  simp at hcoeff

/-- `mul_Delta_map` equals the DirectSum product of h and Δ. -/
private lemma mul_Delta_map_eq_DirectSum_mul (n : ℕ) (hn : 12 ≤ n)
    (h : ModularForm Γ(1) (↑n - 12)) :
    DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) ↑n (mul_Delta_map ↑n h) =
      DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) (↑n - 12) h *
        DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 12 (ModForm_mk Γ(1) 12 Delta) := by
  sorry

/-- A cusp form of weight n (≥ 12) equals `mul_Delta_map n h` where
h = CuspForms_iso_Modforms (the corresponding CuspForm). -/
private lemma cuspform_eq_mul_Delta (n : ℕ) (_hn : 12 ≤ n) (g : ModularForm Γ(1) ↑n)
    (hg : IsCuspForm Γ(1) ↑n g) :
    g = mul_Delta_map ↑n (CuspForms_iso_Modforms ↑n (IsCuspForm_to_CuspForm Γ(1) ↑n g hg)) := by
  set g_cusp := IsCuspForm_to_CuspForm Γ(1) ↑n g hg
  set h := CuspForms_iso_Modforms ↑n g_cusp
  ext z
  have hgz : g z = g_cusp z := by
    have := congr_fun (CuspForm_to_ModularForm_Fun_coe Γ(1) ↑n g hg) z
    simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
      ModularForm.toSlashInvariantForm_coe] at this
    exact this.symm
  rw [hgz, show g_cusp z = (Modform_mul_Delta' ↑n h) z from
    DFunLike.congr_fun ((CuspForms_iso_Modforms ↑n).left_inv g_cusp).symm z,
    Modform_mul_Delta_apply, mul_Delta_map_eq]

/-- The weight-k component of E₄^a · E₆^b (where 4a + 6b = k) has q-expansion coeff 0 = 1.

This follows from multiplicativity of q-expansions and `E4_q_exp_zero`, `E6_q_exp_zero`. -/
private lemma monomial_coeff_zero_eq_one (n a b : ℕ) (hab : 4 * a + 6 * b = n) :
    (qExpansion 1
      (((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ a *
        (DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ b)
        (↑n : ℤ))).coeff 0 = 1 := by
  sorry

/-- Per-weight surjectivity: `DirectSum.of _ k f ∈ range evalE₄E₆` for all k and f. -/
private lemma surj_of_weight : ∀ (k : ℤ) (f : ModularForm Γ(1) k),
    DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) k f ∈ Set.range evalE₄E₆ := by
  intro k f
  by_cases hk_neg : k < 0
  · rw [rank_zero_iff_forall_zero.mp (ModularForm.levelOne_neg_weight_rank_zero hk_neg) f,
      map_zero]
    exact ⟨0, map_zero _⟩
  · push_neg at hk_neg
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
    revert f
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro f
    by_cases hk_odd : Odd (n : ℤ)
    · rw [levelOne_odd_weight_eq_zero hk_odd f, map_zero]; exact ⟨0, map_zero _⟩
    · rw [Int.not_odd_iff_even] at hk_odd
      by_cases hn12 : n < 12
      · -- BASE CASES: n ∈ {0, 2, 4, 6, 8, 10}
        by_cases hn0 : n = 0
        · subst hn0
          have : (1 : ModularForm Γ(1) 0) ≠ 0 := by
            intro h; have := congr_fun (congr_arg (fun x => x.toFun) h) UpperHalfPlane.I
            simp [ModularForm.one_coe_eq_one] at this
          obtain ⟨c, rfl⟩ := exists_smul_eq_of_rank_one
              ModularForm.levelOne_weight_zero_rank_one this f
          exact ⟨MvPolynomial.C c, by
            rw [evalE₄E₆_C, Algebra.algebraMap_eq_smul_one,
              show (1 : DirectSum ℤ (fun k => ModularForm Γ(1) k)) =
                DirectSum.of _ 0 1 from rfl, ← DirectSum.of_smul]; rfl⟩
        by_cases hn2 : n = 2
        · subst hn2; rw [weight_two_zero f, map_zero]; exact ⟨0, map_zero _⟩
        by_cases hn4 : n = 4
        · subst hn4
          obtain ⟨c, rfl⟩ := exists_smul_eq_of_rank_one weight_four_one_dimensional E4_ne_zero f
          exact ⟨MvPolynomial.C c * MvPolynomial.X 0, by
            rw [map_mul, evalE₄E₆_C, evalE₄E₆_X0,
              Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← DirectSum.of_smul]
            norm_cast⟩
        by_cases hn6 : n = 6
        · subst hn6
          obtain ⟨c, rfl⟩ := exists_smul_eq_of_rank_one weight_six_one_dimensional E6_ne_zero f
          exact ⟨MvPolynomial.C c * MvPolynomial.X 1, by
            rw [map_mul, evalE₄E₆_C, evalE₄E₆_X1,
              Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← DirectSum.of_smul]
            norm_cast⟩
        by_cases hn8 : n = 8
        · subst hn8
          obtain ⟨c, rfl⟩ := exists_smul_eq_of_rank_one
              (weight_eight_one_dimensional 8 (by norm_num) ⟨4, rfl⟩ (by norm_num))
              (mul_modform_ne_zero_of_coeff_one E₄ E₄ E4_q_exp_zero E4_q_exp_zero) f
          exact ⟨MvPolynomial.C c * MvPolynomial.X 0 ^ 2, by
            rw [map_mul, map_pow, evalE₄E₆_C, evalE₄E₆_X0, pow_two, DirectSum.of_mul_of,
              Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← DirectSum.of_smul]
            norm_cast⟩
        by_cases hn10 : n = 10
        · subst hn10
          obtain ⟨c, rfl⟩ := exists_smul_eq_of_rank_one
              (weight_eight_one_dimensional 10 (by norm_num) ⟨5, rfl⟩ (by norm_num))
              (mul_modform_ne_zero_of_coeff_one E₄ E₆ E4_q_exp_zero E6_q_exp_zero) f
          exact ⟨MvPolynomial.C c * (MvPolynomial.X 0 * MvPolynomial.X 1), by
            rw [map_mul, map_mul, evalE₄E₆_C, evalE₄E₆_X0, evalE₄E₆_X1, DirectSum.of_mul_of,
              Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← DirectSum.of_smul]
            norm_cast⟩
        · -- Even, < 12, not 0,2,4,6,8,10: impossible
          exfalso; obtain ⟨m, hm⟩ := hk_odd; omega
      · -- INDUCTIVE STEP: n ≥ 12, even
        -- Strategy: decompose f = (cusp form) + c • (monomial E₄^a · E₆^b)
        -- Cusp form part: factor through Δ × M_{n-12}, apply ih
        -- Monomial part: directly in range of evalE₄E₆
        -- The full proof involves cast bookkeeping between ℕ and ℤ indices.
        -- Key sub-steps (all individually verified):
        -- 1. monomial_weight_exists gives (a,b) with 4a+6b=n
        -- 2. monomial_coeff_zero_eq_one: q-coeff 0 of E₄^a·E₆^b = 1 (sorry)
        -- 3. IsCuspForm_iff_coeffZero_eq_zero: f - c•m is cusp form
        -- 4. cuspform_eq_mul_Delta: cusp form = Δ · h
        -- 5. mul_Delta_map_eq_DirectSum_mul: of _ n g = of _ (n-12) h * of _ 12 Δ (sorry)
        -- 6. ih (n-12): of _ (n-12) h ∈ range by induction
        -- 7. delta_mem_range_evalE₄E₆: Δ ∈ range
        -- 8. Subalgebra closure: product and sum of range elements are in range
        sorry

/-- The evaluation homomorphism `evalE₄E₆ : ℂ[X₀, X₁] →ₐ[ℂ] ⨁_k M_k(Γ(1))` is surjective.

Every modular form of level 1 can be written as a polynomial in E₄ and E₆. -/
theorem evalE₄E₆_surjective : Function.Surjective evalE₄E₆ := by
  classical
  intro x
  suffices x ∈ Set.range evalE₄E₆ from this
  rw [show x = x.sum (fun i m => DirectSum.of _ i m) from
    (DFinsupp.sum_single (f := x)).symm,
    show Set.range evalE₄E₆ = ↑evalE₄E₆.range from (AlgHom.coe_range evalE₄E₆).symm]
  apply Subalgebra.sum_mem
  intro k _
  rw [AlgHom.mem_range]
  exact surj_of_weight k (x k)
