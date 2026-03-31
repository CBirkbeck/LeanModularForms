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
  rw [DirectSum.of_mul_of]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  have hind : (↑n : ℤ) - 12 + 12 = ↑n := by omega
  apply ModularForm.gradedMonoid_eq_of_cast hind.symm
  simp only [GradedMonoid.mk, mul_Delta_map]
  ext z
  simp [GradedMonoid.GMul.mul, ModularForm.mul, ModularForm.mcast]
  rfl

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
  subst hab
  have hab' : (↑(4 * a + 6 * b) : ℤ) = ↑a * 4 + ↑b * 6 := by push_cast; ring
  rw [hab']
  rw [DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
  convert_to (qExpansion 1 (⇑(GradedMonoid.GMul.mul (GradedMonoid.GMonoid.gnpow a E₄)
      (GradedMonoid.GMonoid.gnpow b E₆)))).coeff 0 = 1 using 2
  · simp [DirectSum.of_eq_same]
  change (qExpansion 1 (⇑((GradedMonoid.GMonoid.gnpow a E₄).mul
      (GradedMonoid.GMonoid.gnpow b E₆)))).coeff 0 = 1
  have hqm := qExpansion_mul_coeff 1 (a • (4 : ℤ)) (b • (6 : ℤ))
      (GradedMonoid.GMonoid.gnpow a E₄) (GradedMonoid.GMonoid.gnpow b E₆)
  simp only [Nat.cast_one] at hqm
  rw [hqm]
  have hgnpow4 : (GradedMonoid.GMonoid.gnpow a E₄ : ModularForm Γ(1) (a • 4)) =
      ((DirectSum.of _ 4 E₄) ^ a) (a • (4 : ℤ)) := by
    rw [DirectSum.ofPow]; simp [DirectSum.of_eq_same]
  have hgnpow6 : (GradedMonoid.GMonoid.gnpow b E₆ : ModularForm Γ(1) (b • 6)) =
      ((DirectSum.of _ 6 E₆) ^ b) (b • (6 : ℤ)) := by
    rw [DirectSum.ofPow]; simp [DirectSum.of_eq_same]
  simp_rw [hgnpow4, hgnpow6]
  show (qExpansion 1 ⇑(((DirectSum.of _ 4 E₄) ^ a) (↑a * 4)) *
       qExpansion 1 ⇑(((DirectSum.of _ 6 E₆) ^ b) (↑b * 6))).coeff 0 = 1
  rw [qExpansion_pow, qExpansion_pow]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow]
  have hc4 : PowerSeries.constantCoeff (qExpansion 1 (⇑E₄)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact E4_q_exp_zero
  have hc6 : PowerSeries.constantCoeff (qExpansion 1 (⇑E₆)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact E6_q_exp_zero
  simp [hc4, hc6]

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
        push_neg at hn12
        have hk_even_nat : Even n := by exact_mod_cast hk_odd
        obtain ⟨a, b, hab⟩ := monomial_weight_exists n (by omega) hk_even_nat
        -- The monomial E₄^a · E₆^b as a DirectSum element
        set mo := ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ a *
          (DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ b)
        -- Its weight-n component
        set mn := mo (↑n : ℤ)
        set c := (qExpansion 1 f).coeff 0
        have hmn_coeff : (qExpansion 1 mn).coeff 0 = 1 :=
          monomial_coeff_zero_eq_one n a b hab
        -- Step 1: f - c • mn is a cusp form (q-coeff 0 vanishes)
        have hg_cusp : IsCuspForm Γ(1) ↑n (f - c • mn) := by
          rw [IsCuspForm_iff_coeffZero_eq_zero]
          set Q := qExpansionAddHom (show (0 : ℝ) < (1 : ℝ) by norm_num)
            (show (1 : ℝ) ∈ Γ(1).strictPeriods from by simp) (↑n)
          have hQ_smul : Q (c • mn) = c • Q mn :=
            qExpansion_smul (by norm_num : (0 : ℝ) < 1)
              (by simp : (1 : ℝ) ∈ Γ(1).strictPeriods) c mn
          change (Q (f - c • mn)).coeff 0 = 0
          rw [map_sub, hQ_smul]
          rw [show Q f = qExpansion 1 f from rfl, show Q mn = qExpansion 1 mn from rfl]
          rw [map_sub, map_smul, smul_eq_mul, hmn_coeff, mul_one, sub_self]
        set g := f - c • mn
        -- Step 2: Factor g through Δ
        have hcast : (↑n : ℤ) - 12 = (↑(n - 12) : ℤ) := by omega
        set h' := CuspForms_iso_Modforms ↑n (IsCuspForm_to_CuspForm Γ(1) ↑n g hg_cusp)
        have hg_eq : g = mul_Delta_map ↑n h' :=
          cuspform_eq_mul_Delta n (by omega) g hg_cusp
        have hg_ds : DirectSum.of _ (↑n : ℤ) g =
            DirectSum.of _ ((↑n : ℤ) - 12) h' *
            DirectSum.of _ 12 (ModForm_mk Γ(1) 12 Delta) := by
          rw [hg_eq]; exact mul_Delta_map_eq_DirectSum_mul n (by omega) h'
        -- Step 3: Transport h' across the ℤ cast for induction
        have hof_cast : DirectSum.of _ ((↑n : ℤ) - 12) h' =
            DirectSum.of _ (↑(n - 12) : ℤ) (hcast ▸ h') := by
          have : ∀ (k1 k2 : ℤ) (hk : k1 = k2) (x : ModularForm Γ(1) k1),
            DirectSum.of _ k1 x = DirectSum.of _ k2 (hk ▸ x) := by
            intros k1 k2 hk x; subst hk; rfl
          exact this _ _ hcast h'
        -- Step 4: Apply induction hypothesis to h' (weight n - 12)
        have hih : DirectSum.of _ ((↑n : ℤ) - 12) h' ∈ Set.range evalE₄E₆ := by
          rw [hof_cast]; exact ih (n - 12) (by omega) (by omega) (hcast ▸ h')
        have hdelta := delta_mem_range_evalE₄E₆
        -- Step 5: g is in range (product of ih and Δ)
        have hg_in : DirectSum.of _ (↑n : ℤ) g ∈ Set.range evalE₄E₆ := by
          rw [hg_ds]
          obtain ⟨p1, hp1⟩ := hih
          obtain ⟨p2, hp2⟩ := hdelta
          exact ⟨p1 * p2, by rw [map_mul, hp1, hp2]⟩
        -- Step 6: The monomial mo is in range
        have hmn_in : mo ∈ Set.range evalE₄E₆ :=
          ⟨MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b, by
            rw [map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1]⟩
        -- Step 7: of _ n mn = mo (monomial is supported at weight n)
        have hmn_eq : DirectSum.of _ (↑n : ℤ) mn = mo := by
          simp only [mn, mo]
          rw [DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
          have hk' : a • (4 : ℤ) + b • (6 : ℤ) = ↑n := by simp; linarith
          rw [show (↑n : ℤ) = a • (4 : ℤ) + b • (6 : ℤ) from hk'.symm,
            DirectSum.of_eq_same]
        -- Step 8: Combine f = g + c • mn, both parts in range
        have hf_eq : f = g + c • mn := by simp [g]
        have hf_ds : DirectSum.of _ (↑n : ℤ) f =
            DirectSum.of _ (↑n : ℤ) g + c • DirectSum.of _ (↑n : ℤ) mn := by
          rw [hf_eq, map_add, ← DirectSum.of_smul]
        rw [hf_ds, hmn_eq]
        obtain ⟨p1, hp1⟩ := hg_in
        obtain ⟨p2, hp2⟩ := hmn_in
        exact ⟨p1 + MvPolynomial.C c * p2, by
          rw [map_add, hp1, map_mul, evalE₄E₆_C, hp2,
            Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]⟩

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

/-! ## Injectivity of evalE₄E₆

The proof decomposes a polynomial into its weighted-homogeneous components
(with respect to the weight function `![4, 6]`), shows each component maps
independently to a single graded piece of the direct sum, and establishes
per-weight injectivity by strong induction on the weight.

The grading property ensures that `evalE₄E₆ p = 0` implies each
weighted-homogeneous component maps to zero. Per-weight injectivity follows
from the surjectivity proof together with the dimension formulas for `M_k(Γ(1))`,
which show that the evaluation map between the weight-k polynomial subspace
and `M_k(Γ(1))` is a surjection between finite-dimensional spaces of equal
dimension, hence is also injective. -/

/-- Weight function for the graded decomposition of `ℂ[X₀, X₁]` matching `evalE₄E₆`. -/
private def E₄E₆W : Fin 2 → ℕ := ![4, 6]

/-- Every monomial `C c * X₀^a * X₁^b` maps to a DirectSum element supported at
grade `a * 4 + b * 6`. -/
private lemma evalE₄E₆_mono_grade (a b : ℕ) (k : ℤ) (hk : k ≠ (↑a * 4 + ↑b * 6 : ℤ)) :
    (evalE₄E₆ (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) k = 0 := by
  rw [map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1,
    DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
  exact DirectSum.of_eq_of_ne _ _ _ (by omega)

/-- Express a monomial `MvPolynomial.monomial d c` (for `d : Fin 2 →₀ ℕ`) in terms of
`C c * X 0 ^ d 0 * X 1 ^ d 1`. -/
private lemma monomial_fin2_eq (d : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.monomial d c =
    MvPolynomial.C c * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 := by
  rw [MvPolynomial.monomial_eq, mul_assoc]; congr 1
  rw [Finsupp.prod, Finset.prod_subset (fun _ _ => Finset.mem_univ _)
    (fun i _ hi => by
      have : d i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi
      rw [this, pow_zero])]
  simp [Fin.prod_univ_two]

/-- The grading property for a single monomial in `Finsupp` form. -/
private lemma evalE₄E₆_monomial_grade (d : Fin 2 →₀ ℕ) (c : ℂ) (k : ℤ)
    (hk : k ≠ (↑(d 0) * 4 + ↑(d 1) * 6 : ℤ)) :
    (evalE₄E₆ (MvPolynomial.monomial d c)) k = 0 := by
  rw [monomial_fin2_eq, show MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d 0 *
    MvPolynomial.X (1 : Fin 2) ^ d 1 =
    MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1)
    from mul_assoc _ _ _]
  rw [map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    DirectSum.smul_apply, evalE₄E₆_mono_grade (d 0) (d 1) k hk, smul_zero]

/-- The `Finsupp.weight` of a multi-index `d : Fin 2 →₀ ℕ` with respect to `E₄E₆W = ![4, 6]`
equals `d 0 * 4 + d 1 * 6` when cast to `ℤ`. -/
private lemma weight_fin2_cast (d : Fin 2 →₀ ℕ) :
    (Finsupp.weight E₄E₆W d : ℤ) = ↑(d 0) * 4 + ↑(d 1) * 6 := by
  have : Finsupp.weight E₄E₆W d = d 0 * 4 + d 1 * 6 := by
    show (Finsupp.linearCombination ℕ E₄E₆W).toAddMonoidHom d = d 0 * 4 + d 1 * 6
    simp only [LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply]
    rw [d.sum_fintype (fun i a => a • E₄E₆W i) (fun i => by simp)]
    simp [Fin.sum_univ_two, E₄E₆W, mul_comm]
  rw [this]; push_cast; ring

/-- The grading property: if `p` is `E₄E₆W`-weighted-homogeneous of weight `n`,
then `evalE₄E₆ p` is supported only at grade `n` in the direct sum. -/
private lemma evalE₄E₆_whc_grade (n : ℕ) (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆W p n) (k : ℤ) (hk : k ≠ ↑n) :
    (evalE₄E₆ p) k = 0 := by
  rw [← MvPolynomial.support_sum_monomial_coeff p, map_sum, DFinsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  apply evalE₄E₆_monomial_grade
  intro heq; apply hk
  have hwd := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [heq, ← weight_fin2_cast d, hwd]

/-- The grade-`n` component of `evalE₄E₆(p)` equals the grade-`n` component of
`evalE₄E₆` applied to the weight-`n` homogeneous component of `p`. -/
private lemma evalE₄E₆_component_eq (p : MvPolynomial (Fin 2) ℂ) (n : ℕ) :
    (evalE₄E₆ (MvPolynomial.weightedHomogeneousComponent E₄E₆W n p)) (↑n : ℤ) =
    (evalE₄E₆ p) (↑n : ℤ) := by
  -- p = whc n p + (p - whc n p), so evalE₄E₆ p = evalE₄E₆ (whc n p) + evalE₄E₆ (p - whc n p)
  -- At grade n: (evalE₄E₆ p) n = (evalE₄E₆ (whc n p)) n + (evalE₄E₆ (p - whc n p)) n
  -- Need: (evalE₄E₆ (p - whc n p)) n = 0
  have hdecomp : p = MvPolynomial.weightedHomogeneousComponent E₄E₆W n p +
    (p - MvPolynomial.weightedHomogeneousComponent E₄E₆W n p) := by ring
  -- Show: (evalE₄E₆ (p - whc n p)) (↑n) = 0
  -- Every monomial in (p - whc n p) has weight ≠ n
  set q := p - MvPolynomial.weightedHomogeneousComponent E₄E₆W n p
  conv_rhs => rw [hdecomp, map_add, DFinsupp.add_apply]
  suffices h : (evalE₄E₆ q) (↑n : ℤ) = 0 by rw [h, add_zero]
  rw [← MvPolynomial.support_sum_monomial_coeff q, map_sum, DFinsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  apply evalE₄E₆_monomial_grade
  intro heq
  -- d ∈ support of q, so coeff d q ≠ 0
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  -- coeff d q = coeff d p - coeff d (whc n p)
  -- If weight(d) = n, then coeff d (whc n p) = coeff d p, so coeff d q = 0, contradiction.
  have : Finsupp.weight E₄E₆W d = n := by
    have h := weight_fin2_cast d
    omega
  exfalso; apply hcoeff
  simp only [q, MvPolynomial.coeff_sub]
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos this, sub_self]

/-- Per-weight injectivity: if `p` is `E₄E₆W`-weighted-homogeneous of weight `n`
and `evalE₄E₆(p)` vanishes at grade `n`, then `p = 0`.

Equivalently, the monomials `{E₄^a · E₆^b : 4a + 6b = n}` are linearly independent
in `M_n(Γ(1))`. This follows from the fact that both the space of weight-`n`
polynomials and `M_n(Γ(1))` satisfy the same dimension recurrence
`d(k) = 1 + d(k - 12)` for `k ≥ 12` even (with matching base cases), and
`evalE₄E₆` is surjective on each weight (from `surj_of_weight`). A surjective
linear map between finite-dimensional spaces of equal dimension is injective. -/
private lemma per_weight_injective : ∀ (n : ℕ) (p : MvPolynomial (Fin 2) ℂ),
    MvPolynomial.IsWeightedHomogeneous E₄E₆W p n →
    (evalE₄E₆ p) (↑n : ℤ) = 0 → p = 0 := by
  sorry

/-- The evaluation homomorphism `evalE₄E₆` is injective (E₄ and E₆ are algebraically
independent). The proof decomposes a polynomial into weighted-homogeneous components,
uses the grading property to reduce to per-weight injectivity, and establishes the
latter by strong induction on the weight. -/
theorem evalE₄E₆_injective : Function.Injective evalE₄E₆ := by
  intro p q hpq
  rw [← sub_eq_zero]
  set r := p - q with hr_def
  have hr : evalE₄E₆ r = 0 := by rw [map_sub, sub_eq_zero]; exact hpq
  -- Decompose r into weighted-homogeneous components
  rw [← MvPolynomial.sum_weightedHomogeneousComponent E₄E₆W r]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  exact per_weight_injective n _
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    (by rw [evalE₄E₆_component_eq]; rw [hr]; rfl)

/-! ## Main isomorphism and corollaries -/

/-- The graded ring of level 1 modular forms is isomorphic to the weighted polynomial
ring in E₄ (weight 4) and E₆ (weight 6).

This is the classical structure theorem: every modular form for SL₂(ℤ) is a polynomial
in the Eisenstein series E₄ and E₆, and E₄, E₆ are algebraically independent. -/
noncomputable def modularFormsEquivMvPolynomial :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ]
      DirectSum ℤ (fun k => ModularForm (CongruenceSubgroup.Gamma 1) k) :=
  AlgEquiv.ofBijective evalE₄E₆ ⟨evalE₄E₆_injective, evalE₄E₆_surjective⟩

/-- E₄ and E₆ generate the entire graded ring of level 1 modular forms. -/
theorem E₄E₆_generate :
    Algebra.adjoin ℂ
      ({DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄,
        DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆} :
        Set (DirectSum ℤ (fun k => ModularForm (CongruenceSubgroup.Gamma 1) k))) = ⊤ := by
  rw [show ({DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄,
        DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆} : Set _) =
      Set.range (![DirectSum.of _ 4 E₄, DirectSum.of _ 6 E₆] : Fin 2 → _)
    from (Matrix.range_cons_cons_empty _ _ _).symm,
    Algebra.adjoin_range_eq_range_aeval,
    show MvPolynomial.aeval (![DirectSum.of _ 4 E₄, DirectSum.of _ 6 E₆] : Fin 2 → _) = evalE₄E₆
    from rfl]
  exact (AlgHom.range_eq_top evalE₄E₆).mpr evalE₄E₆_surjective
