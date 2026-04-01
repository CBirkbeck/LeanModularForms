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

/-- Evaluation homomorphism sending `ℂ[X₀, X₁]` to the graded ring of level 1 modular forms via `X₀ ↦ E₄` and `X₁ ↦ E₆`. -/
noncomputable def evalE₄E₆ :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ]
      DirectSum ℤ (fun k => ModularForm (CongruenceSubgroup.Gamma 1) k) :=
  MvPolynomial.aeval
    ![DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 4 E₄,
      DirectSum.of (fun k : ℤ => ModularForm (CongruenceSubgroup.Gamma 1) k) 6 E₆]

/-- The polynomial `Δ_poly = (1/1728)(X₀³ - X₁²)` in `ℂ[X₀, X₁]`, mapping to `Δ` under `evalE₄E₆`. -/
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

private lemma mul_Delta_map_eq_DirectSum_mul (n : ℕ) (_hn : 12 ≤ n)
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
  simp only [mcast, mul, GradedMonoid.GMul.mul]
  rfl

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
  change (qExpansion 1 ⇑(((DirectSum.of _ 4 E₄) ^ a) (↑a * 4)) *
       qExpansion 1 ⇑(((DirectSum.of _ 6 E₆) ^ b) (↑b * 6))).coeff 0 = 1
  rw [qExpansion_pow, qExpansion_pow]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow]
  have hc4 : PowerSeries.constantCoeff (qExpansion 1 (⇑E₄)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact E4_q_exp_zero
  have hc6 : PowerSeries.constantCoeff (qExpansion 1 (⇑E₆)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact E6_q_exp_zero
  simp [hc4, hc6]

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
      · by_cases hn0 : n = 0
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
        · exfalso; obtain ⟨m, hm⟩ := hk_odd; omega
      · push_neg at hn12
        have hk_even_nat : Even n := by exact_mod_cast hk_odd
        obtain ⟨a, b, hab⟩ := monomial_weight_exists n (by omega) hk_even_nat
        set mo := ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ a *
          (DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ b)
        set mn := mo (↑n : ℤ)
        set c := (qExpansion 1 f).coeff 0
        have hmn_coeff : (qExpansion 1 mn).coeff 0 = 1 :=
          monomial_coeff_zero_eq_one n a b hab
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
        have hcast : (↑n : ℤ) - 12 = (↑(n - 12) : ℤ) := by omega
        set h' := CuspForms_iso_Modforms ↑n (IsCuspForm_to_CuspForm Γ(1) ↑n g hg_cusp)
        have hg_eq : g = mul_Delta_map ↑n h' :=
          cuspform_eq_mul_Delta n (by omega) g hg_cusp
        have hg_ds : DirectSum.of _ (↑n : ℤ) g =
            DirectSum.of _ ((↑n : ℤ) - 12) h' *
            DirectSum.of _ 12 (ModForm_mk Γ(1) 12 Delta) := by
          rw [hg_eq]; exact mul_Delta_map_eq_DirectSum_mul n (by omega) h'
        have hof_cast : DirectSum.of _ ((↑n : ℤ) - 12) h' =
            DirectSum.of _ (↑(n - 12) : ℤ) (hcast ▸ h') := by
          have : ∀ (k1 k2 : ℤ) (hk : k1 = k2) (x : ModularForm Γ(1) k1),
            DirectSum.of _ k1 x = DirectSum.of _ k2 (hk ▸ x) := by
            intros k1 k2 hk x; subst hk; rfl
          exact this _ _ hcast h'
        have hih : DirectSum.of _ ((↑n : ℤ) - 12) h' ∈ Set.range evalE₄E₆ := by
          rw [hof_cast]; exact ih (n - 12) (by omega) (by omega) (hcast ▸ h')
        have hdelta := delta_mem_range_evalE₄E₆
        have hg_in : DirectSum.of _ (↑n : ℤ) g ∈ Set.range evalE₄E₆ := by
          rw [hg_ds]
          obtain ⟨p1, hp1⟩ := hih
          obtain ⟨p2, hp2⟩ := hdelta
          exact ⟨p1 * p2, by rw [map_mul, hp1, hp2]⟩
        have hmn_in : mo ∈ Set.range evalE₄E₆ :=
          ⟨MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b, by
            rw [map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1]⟩
        have hmn_eq : DirectSum.of _ (↑n : ℤ) mn = mo := by
          simp only [mn, mo]
          rw [DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
          have hk' : a • (4 : ℤ) + b • (6 : ℤ) = ↑n := by simp; linarith
          rw [show (↑n : ℤ) = a • (4 : ℤ) + b • (6 : ℤ) from hk'.symm,
            DirectSum.of_eq_same]
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

/-- The evaluation homomorphism `evalE₄E₆ : ℂ[X₀, X₁] →ₐ[ℂ] ⨁_k M_k(Γ(1))` is surjective. -/
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

private lemma evalE₄E₆_mono_grade (a b : ℕ) (k : ℤ) (hk : k ≠ (↑a * 4 + ↑b * 6 : ℤ)) :
    (evalE₄E₆ (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) k = 0 := by
  rw [map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1,
    DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
  exact DirectSum.of_eq_of_ne _ _ _ (by omega)

private lemma monomial_fin2_eq (d : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.monomial d c =
    MvPolynomial.C c * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 := by
  rw [MvPolynomial.monomial_eq, mul_assoc]; congr 1
  rw [Finsupp.prod, Finset.prod_subset (fun _ _ => Finset.mem_univ _)
    (fun i _ hi => by
      have : d i = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hi
      rw [this, pow_zero])]
  simp [Fin.prod_univ_two]

private lemma evalE₄E₆_monomial_grade (d : Fin 2 →₀ ℕ) (c : ℂ) (k : ℤ)
    (hk : k ≠ (↑(d 0) * 4 + ↑(d 1) * 6 : ℤ)) :
    (evalE₄E₆ (MvPolynomial.monomial d c)) k = 0 := by
  rw [monomial_fin2_eq, show MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d 0 *
    MvPolynomial.X (1 : Fin 2) ^ d 1 =
    MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1)
    from mul_assoc _ _ _]
  rw [map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    DirectSum.smul_apply, evalE₄E₆_mono_grade (d 0) (d 1) k hk, smul_zero]

private lemma weight_fin2_cast (d : Fin 2 →₀ ℕ) :
    (Finsupp.weight E₄E₆Weight d : ℤ) = ↑(d 0) * 4 + ↑(d 1) * 6 := by
  have : Finsupp.weight E₄E₆Weight d = d 0 * 4 + d 1 * 6 := by
    change (Finsupp.linearCombination ℕ E₄E₆Weight).toAddMonoidHom d = d 0 * 4 + d 1 * 6
    simp only [LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply]
    rw [d.sum_fintype (fun i a => a • E₄E₆Weight i) (fun i => by simp)]
    simp [Fin.sum_univ_two, E₄E₆Weight, mul_comm]
  rw [this]; push_cast; ring

private lemma evalE₄E₆_whc_grade (n : ℕ) (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n) (k : ℤ) (hk : k ≠ ↑n) :
    (evalE₄E₆ p) k = 0 := by
  rw [← MvPolynomial.support_sum_monomial_coeff p, map_sum, DFinsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  apply evalE₄E₆_monomial_grade
  intro heq; apply hk
  have hwd := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [heq, ← weight_fin2_cast d, hwd]

private lemma evalE₄E₆_component_eq (p : MvPolynomial (Fin 2) ℂ) (n : ℕ) :
    (evalE₄E₆ (MvPolynomial.weightedHomogeneousComponent E₄E₆Weight n p)) (↑n : ℤ) =
    (evalE₄E₆ p) (↑n : ℤ) := by
  have hdecomp : p = MvPolynomial.weightedHomogeneousComponent E₄E₆Weight n p +
    (p - MvPolynomial.weightedHomogeneousComponent E₄E₆Weight n p) := by ring
  set q := p - MvPolynomial.weightedHomogeneousComponent E₄E₆Weight n p
  conv_rhs => rw [hdecomp, map_add, DFinsupp.add_apply]
  suffices h : (evalE₄E₆ q) (↑n : ℤ) = 0 by rw [h, add_zero]
  rw [← MvPolynomial.support_sum_monomial_coeff q, map_sum, DFinsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  apply evalE₄E₆_monomial_grade
  intro heq
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  have : Finsupp.weight E₄E₆Weight d = n := by
    have h := weight_fin2_cast d
    omega
  exfalso; apply hcoeff
  simp only [q, MvPolynomial.coeff_sub]
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos this, sub_self]

private lemma no_wt_monomial_of_odd {n : ℕ} (hn : Odd n) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight E₄E₆Weight d ≠ n := by
  intro h
  have : Finsupp.weight E₄E₆Weight d = d 0 * 4 + d 1 * 6 := by
    change (Finsupp.linearCombination ℕ E₄E₆Weight).toAddMonoidHom d = d 0 * 4 + d 1 * 6
    simp only [LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply]
    rw [d.sum_fintype (fun i a => a • E₄E₆Weight i) (fun i => by simp)]
    simp [Fin.sum_univ_two, E₄E₆Weight, mul_comm]
  rw [this] at h
  have hev : Even n := ⟨d 0 * 2 + d 1 * 3, by omega⟩
  simp [Nat.even_iff, Nat.odd_iff] at hev hn; omega

private lemma no_wt_monomial_of_two (d : Fin 2 →₀ ℕ) :
    Finsupp.weight E₄E₆Weight d ≠ 2 := by
  intro h
  have : Finsupp.weight E₄E₆Weight d = d 0 * 4 + d 1 * 6 := by
    change (Finsupp.linearCombination ℕ E₄E₆Weight).toAddMonoidHom d = d 0 * 4 + d 1 * 6
    simp only [LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply]
    rw [d.sum_fintype (fun i a => a • E₄E₆Weight i) (fun i => by simp)]
    simp [Fin.sum_univ_two, E₄E₆Weight, mul_comm]
  rw [this] at h; omega

private lemma whomog_eq_zero_of_no_monomials {n : ℕ} (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (hno : ∀ d : Fin 2 →₀ ℕ, Finsupp.weight E₄E₆Weight d ≠ n) : p = 0 := by
  rw [← MvPolynomial.support_eq_empty]
  by_contra h
  obtain ⟨d, hd⟩ := Finset.nonempty_of_ne_empty h
  exact hno d (hp (MvPolynomial.mem_support_iff.mp hd))

private lemma weight_eq_4a_6b (d : Fin 2 →₀ ℕ) :
    Finsupp.weight E₄E₆Weight d = d 0 * 4 + d 1 * 6 := by
  change (Finsupp.linearCombination ℕ E₄E₆Weight).toAddMonoidHom d = d 0 * 4 + d 1 * 6
  simp only [LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply]
  rw [d.sum_fintype (fun i a => a • E₄E₆Weight i) (fun i => by simp)]
  simp [Fin.sum_univ_two, E₄E₆Weight, mul_comm]

private lemma finsupp_of_fin2 (a b : ℕ) :
    ∃ d : Fin 2 →₀ ℕ, d 0 = a ∧ d 1 = b := by
  exact ⟨Finsupp.equivFunOnFinite.invFun ![a, b], by simp [Matrix.cons_val_zero],
    by simp [Matrix.cons_val_one]⟩

private lemma whomog_unique_monomial {n : ℕ} (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (d₀ : Fin 2 →₀ ℕ) (hd₀ : Finsupp.weight E₄E₆Weight d₀ = n)
    (huniq : ∀ d : Fin 2 →₀ ℕ, Finsupp.weight E₄E₆Weight d = n → d = d₀) :
    p = MvPolynomial.monomial d₀ (MvPolynomial.coeff d₀ p) := by
  ext d
  by_cases hd : d = d₀
  · subst hd; simp
  · rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hd)]
    have : Finsupp.weight E₄E₆Weight d ≠ n := fun h => hd (huniq d h)
    exact hp.coeff_eq_zero d this

private lemma per_weight_injective_unique_monomial {n : ℕ} (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0)
    (d₀ : Fin 2 →₀ ℕ) (hd₀ : Finsupp.weight E₄E₆Weight d₀ = n)
    (huniq : ∀ d : Fin 2 →₀ ℕ, Finsupp.weight E₄E₆Weight d = n → d = d₀)
    (hmf_ne : ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ (d₀ 0) *
      (DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ (d₀ 1))
      (↑n : ℤ) ≠ 0) : p = 0 := by
  have hpc := whomog_unique_monomial p hp d₀ hd₀ huniq
  rw [hpc] at heval ⊢
  rw [monomial_fin2_eq, show MvPolynomial.C (MvPolynomial.coeff d₀ p) *
    MvPolynomial.X (0 : Fin 2) ^ d₀ 0 * MvPolynomial.X (1 : Fin 2) ^ d₀ 1 =
    MvPolynomial.C (MvPolynomial.coeff d₀ p) *
    (MvPolynomial.X (0 : Fin 2) ^ d₀ 0 * MvPolynomial.X (1 : Fin 2) ^ d₀ 1)
    from mul_assoc _ _ _] at heval
  rw [map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1,
    DirectSum.smul_apply] at heval
  rcases smul_eq_zero.mp heval with hc | hmz
  · rw [show MvPolynomial.monomial d₀ (MvPolynomial.coeff d₀ p) =
      MvPolynomial.monomial d₀ 0 from by rw [hc], MvPolynomial.monomial_zero]
  · exact absurd hmz hmf_ne

private lemma X0_cubed_eq : (MvPolynomial.X (0 : Fin 2)) ^ 3 =
    (MvPolynomial.X (1 : Fin 2)) ^ 2 + (1728 : ℂ) • Delta_poly := by
  simp only [Delta_poly, smul_smul]
  norm_num

private lemma Delta_poly_isWeightedHomogeneous :
    MvPolynomial.IsWeightedHomogeneous E₄E₆Weight Delta_poly 12 := by
  unfold Delta_poly
  simp only [MvPolynomial.smul_eq_C_mul]
  intro d hd
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sub] at hd
  have h1 : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight
      (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) ℂ) 12 :=
    show _ from (MvPolynomial.isWeightedHomogeneous_X ℂ E₄E₆Weight (0 : Fin 2)).pow 3
  have h2 : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight
      (MvPolynomial.X (1 : Fin 2) ^ 2 : MvPolynomial (Fin 2) ℂ) 12 :=
    show _ from (MvPolynomial.isWeightedHomogeneous_X ℂ E₄E₆Weight (1 : Fin 2)).pow 2
  by_cases hd3 : MvPolynomial.coeff d (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) ℂ) ≠ 0
  · exact h1 hd3
  · push_neg at hd3
    by_cases hd6 : MvPolynomial.coeff d (MvPolynomial.X (1 : Fin 2) ^ 2 : MvPolynomial (Fin 2) ℂ) ≠ 0
    · exact h2 hd6
    · push_neg at hd6; simp [hd3, hd6] at hd

private lemma mul_Delta_map_injective {k : ℤ} (f : ModularForm Γ(1) (k - 12))
    (hf : mul_Delta_map k f = 0) : f = 0 := by
  ext z
  have hz := congr_fun (congr_arg (fun x => x.toFun) hf) z
  simp only [ModularForm.zero_apply, SlashInvariantForm.toFun_eq_coe,
    ModularForm.toSlashInvariantForm_coe] at hz
  rw [mul_Delta_map_eq] at hz
  exact (mul_eq_zero.mp hz).resolve_right (Δ_ne_zero z)

private lemma monomial_reduction (a b : ℕ) (ha : 3 ≤ a) :
    (MvPolynomial.X (0 : Fin 2) ^ a * MvPolynomial.X (1 : Fin 2) ^ b : MvPolynomial (Fin 2) ℂ) =
    MvPolynomial.X 0 ^ (a - 3) * MvPolynomial.X 1 ^ (b + 2) +
    (1728 : ℂ) • Delta_poly * (MvPolynomial.X 0 ^ (a - 3) * MvPolynomial.X 1 ^ b) := by
  have : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ a =
    MvPolynomial.X 0 ^ (a - 3) * MvPolynomial.X (0 : Fin 2) ^ 3 := by
    rw [← pow_add]; congr 1; omega
  rw [this, X0_cubed_eq]
  ring

private lemma X0_pow_mul_X1_pow_isWeightedHomogeneous (a b n : ℕ) (hab : a * 4 + b * 6 = n) :
    MvPolynomial.IsWeightedHomogeneous E₄E₆Weight
      (MvPolynomial.X (0 : Fin 2) ^ a * MvPolynomial.X (1 : Fin 2) ^ b :
        MvPolynomial (Fin 2) ℂ) n := by
  have h0 := (MvPolynomial.isWeightedHomogeneous_X ℂ E₄E₆Weight (0 : Fin 2)).pow a
  have h1 := (MvPolynomial.isWeightedHomogeneous_X ℂ E₄E₆Weight (1 : Fin 2)).pow b
  convert h0.mul h1 using 1; simp [E₄E₆Weight]; omega

private lemma whomog_poly_Delta_decomp {n : ℕ} (hn12 : 12 ≤ n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n) :
    ∃ r s : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight r n ∧
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight s (n - 12) ∧
      p = r + Delta_poly * s ∧
      (∀ d ∈ r.support, d 0 < 3) := by
  suffices key : ∀ (M : ℕ) (p : MvPolynomial (Fin 2) ℂ),
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n →
      (∑ d ∈ p.support, d 0) ≤ M →
      ∃ r s : MvPolynomial (Fin 2) ℂ,
        MvPolynomial.IsWeightedHomogeneous E₄E₆Weight r n ∧
        MvPolynomial.IsWeightedHomogeneous E₄E₆Weight s (n - 12) ∧
        p = r + Delta_poly * s ∧
        (∀ d ∈ r.support, d 0 < 3) from
    key _ p hp le_rfl
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro p hp hM
  by_cases hall : ∀ d ∈ p.support, d 0 < 3
  · exact ⟨p, 0, hp, (MvPolynomial.isWeightedHomogeneous_zero ℂ E₄E₆Weight (n - 12)),
      by simp, hall⟩
  · push_neg at hall
    obtain ⟨d, hd_mem, hd_ge⟩ := hall
    have hcoeff_ne : MvPolynomial.coeff d p ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd_mem
    have hwd : d 0 * 4 + d 1 * 6 = n := by
      have := hp (MvPolynomial.mem_support_iff.mp hd_mem)
      have := weight_eq_4a_6b d; omega
    set c := MvPolynomial.coeff d p
    set delta_piece := MvPolynomial.C c * ((1728 : ℂ) • Delta_poly *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ (d 1)))
    set p' := p - delta_piece with hp'_def
    have hp_eq : p = p' + delta_piece := by simp [p']
    have hp'_wh : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p' n := by
      rw [hp'_def]
      have hdp_wh : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight delta_piece n := by
        change MvPolynomial.IsWeightedHomogeneous E₄E₆Weight
          (MvPolynomial.C c * ((1728 : ℂ) • Delta_poly *
            (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
              MvPolynomial.X (1 : Fin 2) ^ (d 1)))) n
        apply MvPolynomial.IsWeightedHomogeneous.C_mul
        rw [MvPolynomial.smul_eq_C_mul,
          show MvPolynomial.C (1728 : ℂ) * Delta_poly *
            (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1) =
            MvPolynomial.C (1728 : ℂ) * (Delta_poly *
              (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
                MvPolynomial.X (1 : Fin 2) ^ d 1)) from by ring]
        apply MvPolynomial.IsWeightedHomogeneous.C_mul
        have h12 := Delta_poly_isWeightedHomogeneous
        have hn12' := X0_pow_mul_X1_pow_isWeightedHomogeneous (d 0 - 3) (d 1) (n - 12)
          (by omega)
        convert h12.mul hn12' using 1; omega
      exact (MvPolynomial.mem_weightedHomogeneousSubmodule ℂ E₄E₆Weight n _).mp
        (Submodule.sub_mem _
          ((MvPolynomial.mem_weightedHomogeneousSubmodule ℂ E₄E₆Weight n p).mpr hp)
          ((MvPolynomial.mem_weightedHomogeneousSubmodule ℂ E₄E₆Weight n delta_piece).mpr hdp_wh))
    set q₁ := MvPolynomial.C (c * 1728) *
      (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ (d 1))
    have hdelta_eq : delta_piece = Delta_poly * q₁ := by
      simp only [delta_piece, q₁, MvPolynomial.smul_eq_C_mul, map_mul]; ring
    have hq₁_wh : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight q₁ (n - 12) :=
      MvPolynomial.IsWeightedHomogeneous.C_mul
        (X0_pow_mul_X1_pow_isWeightedHomogeneous (d 0 - 3) (d 1) (n - 12) (by omega)) _
    have hM_lt : ∑ d' ∈ p'.support, d' 0 < ∑ d' ∈ p.support, d' 0 := by
      set d' := Finsupp.single (0 : Fin 2) (d 0 - 3) + Finsupp.single (1 : Fin 2) (d 1 + 2)
        with hd'_def
      have hd_fin : d = Finsupp.single (0 : Fin 2) (d 0) +
          Finsupp.single (1 : Fin 2) (d 1) := by
        ext i; fin_cases i <;> simp [Finsupp.add_apply]
      have hdd' : d ≠ d' := by
        intro heq; have h0 := Finsupp.ext_iff.mp heq (0 : Fin 2)
        simp [hd'_def, Finsupp.add_apply] at h0; omega
      have hdp_mono : delta_piece =
          (MvPolynomial.monomial d) c - (MvPolynomial.monomial d') c := by
        have h1728 : (1728 : ℂ) • Delta_poly =
          MvPolynomial.X (0 : Fin 2) ^ 3 - MvPolynomial.X (1 : Fin 2) ^ 2 := by
          simp only [Delta_poly, smul_smul]; norm_num
        have hdp_simp : delta_piece = MvPolynomial.C c *
          (MvPolynomial.X (0 : Fin 2) ^ 3 - MvPolynomial.X (1 : Fin 2) ^ 2) *
          (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
            MvPolynomial.X (1 : Fin 2) ^ (d 1)) := by
          change MvPolynomial.C c * ((1728 : ℂ) • Delta_poly *
            (MvPolynomial.X 0 ^ (d 0 - 3) * MvPolynomial.X 1 ^ (d 1))) = _
          rw [h1728]; ring
        rw [hdp_simp]
        have h3 : (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) ℂ) *
          (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1) =
          MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1 := by
          have h := show (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ 3 *
              (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1)
            = (MvPolynomial.X (0 : Fin 2) ^ 3 * MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3)) *
                MvPolynomial.X (1 : Fin 2) ^ d 1 from by ring
          rw [h, ← pow_add, show 3 + (d 0 - 3) = d 0 from by omega]
        have h2 : (MvPolynomial.X (1 : Fin 2) ^ 2 : MvPolynomial (Fin 2) ℂ) *
          (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1) =
          MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
            MvPolynomial.X (1 : Fin 2) ^ (d 1 + 2) := by
          have h := show (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ 2 *
              (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1)
            = MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
                (MvPolynomial.X (1 : Fin 2) ^ d 1 * MvPolynomial.X (1 : Fin 2) ^ 2) from by
                  ring
          rw [h, ← pow_add]
        rw [show MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) ^ 3 -
            MvPolynomial.X (1 : Fin 2) ^ 2) *
            (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
              MvPolynomial.X (1 : Fin 2) ^ d 1) =
          MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) ^ 3 *
            (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1)) -
          MvPolynomial.C c * (MvPolynomial.X (1 : Fin 2) ^ 2 *
            (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
              MvPolynomial.X (1 : Fin 2) ^ d 1)) from by ring,
          h3, h2]
        congr 1
        · rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
            MvPolynomial.monomial_mul, one_mul, MvPolynomial.C_mul_monomial, mul_one]
          exact congrArg (· c) (congrArg MvPolynomial.monomial hd_fin.symm)
        · rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
            MvPolynomial.monomial_mul, one_mul, MvPolynomial.C_mul_monomial, mul_one]
      have hcoeff_d_p' : MvPolynomial.coeff d p' = 0 := by
        rw [hp'_def, MvPolynomial.coeff_sub, hdp_mono, MvPolynomial.coeff_sub,
          MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial,
          if_pos rfl, if_neg hdd'.symm, sub_zero, sub_self]
      have hd_not : d ∉ p'.support := MvPolynomial.notMem_support_iff.mpr hcoeff_d_p'
      have hdp_supp : delta_piece.support ⊆ {d, d'} := by
        rw [hdp_mono]
        intro x hx
        have hx_mem := MvPolynomial.support_sub (Fin 2)
          ((MvPolynomial.monomial d) c) ((MvPolynomial.monomial d') c) hx
        simp only [Finset.mem_union] at hx_mem
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hx_mem with hx1 | hx2
        · left
          rw [MvPolynomial.support_monomial] at hx1
          split_ifs at hx1 with hc
          · exact absurd hx1 (Finset.notMem_empty _)
          · exact Finset.mem_singleton.mp hx1
        · right
          rw [MvPolynomial.support_monomial] at hx2
          split_ifs at hx2 with hc
          · exact absurd hx2 (Finset.notMem_empty _)
          · exact Finset.mem_singleton.mp hx2
      have hp'_supp : p'.support ⊆ p.support ∪ {d'} := by
        intro x hx
        have hx_union := MvPolynomial.support_sub (Fin 2) p delta_piece hx
        simp only [Finset.mem_union, Finset.mem_singleton] at hx_union ⊢
        rcases hx_union with h | h
        · exact Or.inl h
        · have := hdp_supp h
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl
          · exact absurd hx hd_not
          · exact Or.inr rfl
      have hd'0 : d' 0 = d 0 - 3 := by simp [hd'_def, Finsupp.add_apply]
      by_cases hd'T : d' ∈ p.support
      · have hS : p'.support ⊆ p.support := by
          intro x hx
          rcases (Finset.mem_union.mp (hp'_supp hx)) with h | h
          · exact h
          · exact Finset.mem_singleton.mp h ▸ hd'T
        calc ∑ x ∈ p'.support, x 0
            ≤ ∑ x ∈ p.support.erase d, x 0 :=
              Finset.sum_le_sum_of_subset (fun x hx =>
                Finset.mem_erase.mpr ⟨fun h => hd_not (h ▸ hx), hS hx⟩)
          _ < ∑ x ∈ p.support.erase d, x 0 + d 0 := by omega
          _ = ∑ x ∈ p.support, x 0 := Finset.sum_erase_add p.support _ hd_mem
      · have hd'_not_erase : d' ∉ p.support.erase d :=
          fun h => hd'T (Finset.mem_of_mem_erase h)
        have hdisj : Disjoint (p.support.erase d) {d'} :=
          Finset.disjoint_singleton_right.mpr hd'_not_erase
        have hTd' : (p.support ∪ {d'}).erase d = p.support.erase d ∪ {d'} := by
          ext x
          simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
          constructor
          · rintro ⟨hne, hx | rfl⟩
            · exact Or.inl ⟨hne, hx⟩
            · exact Or.inr rfl
          · rintro (⟨hne, hx⟩ | rfl)
            · exact ⟨hne, Or.inl hx⟩
            · exact ⟨hdd'.symm, Or.inr rfl⟩
        have hST : p'.support ⊆ p.support.erase d ∪ {d'} := by
          rw [← hTd']
          intro x hx
          exact Finset.mem_erase.mpr ⟨fun h => hd_not (h ▸ hx), hp'_supp hx⟩
        calc ∑ x ∈ p'.support, x 0
            ≤ ∑ x ∈ p.support.erase d ∪ {d'}, x 0 :=
              Finset.sum_le_sum_of_subset hST
          _ = ∑ x ∈ p.support.erase d, x 0 + ∑ x ∈ {d'}, x 0 :=
              Finset.sum_union hdisj
          _ = ∑ x ∈ p.support.erase d, x 0 + d' 0 := by simp
          _ < ∑ x ∈ p.support.erase d, x 0 + d 0 := by omega
          _ = ∑ x ∈ p.support, x 0 := Finset.sum_erase_add p.support _ hd_mem
    obtain ⟨r, s', hr_wh, hs'_wh, hp'_eq, hr_red⟩ :=
      ih (∑ d' ∈ p'.support, d' 0) (by omega) p' hp'_wh le_rfl
    refine ⟨r, s' + q₁, hr_wh, hs'_wh.add hq₁_wh, ?_, hr_red⟩
    rw [hp_eq, hdelta_eq, hp'_eq, mul_add]; ring

private lemma unique_small_weight_soln {a₁ b₁ a₂ b₂ : ℕ}
    (ha₁ : a₁ < 3) (ha₂ : a₂ < 3)
    (h : a₁ * 4 + b₁ * 6 = a₂ * 4 + b₂ * 6) : a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · interval_cases a₁ <;> interval_cases a₂ <;> omega
  · omega

private lemma reduced_poly_is_scalar {n : ℕ} (_hn12 : 12 ≤ n)
    (r : MvPolynomial (Fin 2) ℂ)
    (hr : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight r n)
    (hr_red : ∀ d ∈ r.support, d 0 < 3) :
    ∀ d₁ d₂ : Fin 2 →₀ ℕ, d₁ ∈ r.support → d₂ ∈ r.support → d₁ = d₂ := by
  intro d₁ d₂ hd₁ hd₂
  have hw1 := hr (MvPolynomial.mem_support_iff.mp hd₁)
  have hw2 := hr (MvPolynomial.mem_support_iff.mp hd₂)
  have h46_1 := weight_eq_4a_6b d₁; rw [hw1] at h46_1
  have h46_2 := weight_eq_4a_6b d₂; rw [hw2] at h46_2
  have heq : d₁ 0 * 4 + d₁ 1 * 6 = d₂ 0 * 4 + d₂ 1 * 6 := by linarith
  obtain ⟨hd0, hd1⟩ := unique_small_weight_soln (hr_red d₁ hd₁) (hr_red d₂ hd₂) heq
  ext i; fin_cases i
  · exact hd0
  · exact hd1

private lemma evalE₄E₆_Delta_mul_coeff_zero {n : ℕ} (hn12 : 12 ≤ n)
    (s : MvPolynomial (Fin 2) ℂ)
    (hs : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight s (n - 12)) :
    (qExpansion 1 ↑((evalE₄E₆ (Delta_poly * s)) (↑n : ℤ))).coeff 0 = 0 := by
  rw [map_mul]
  have hD_grade := evalE₄E₆_whc_grade 12 Delta_poly Delta_poly_isWeightedHomogeneous
  have hS_grade := evalE₄E₆_whc_grade (n - 12) s hs
  set D := evalE₄E₆ Delta_poly; set S := evalE₄E₆ s
  have hD_single : D = DirectSum.of _ 12 (D 12) := by
    ext k; by_cases hk : k = 12
    · subst hk; simp [DirectSum.of_eq_same]
    · rw [hD_grade k hk, DirectSum.of_eq_of_ne _ _ _ hk]
  have hS_single : S = DirectSum.of _ (↑(n-12) : ℤ) (S (↑(n-12))) := by
    ext k; by_cases hk : k = (↑(n-12) : ℤ)
    · subst hk; simp [DirectSum.of_eq_same]
    · rw [hS_grade k hk, DirectSum.of_eq_of_ne _ _ _ hk]
  rw [hD_single, hS_single, DirectSum.of_mul_of]
  have hcast : (12 : ℤ) + ↑(n - 12) = ↑n := by omega
  rw [DirectSum.of_apply, dif_pos hcast]
  have hq_eq : qExpansion 1 ↑(hcast ▸ GradedMonoid.GMul.mul (D 12) (S (↑(n-12))) :
      ModularForm Γ(1) (↑n)) =
      qExpansion 1 ↑(GradedMonoid.GMul.mul (D 12) (S (↑(n-12)))) := by
    congr 1; ext z
    have : ∀ {k₁ k₂ : ℤ} (heq : k₁ = k₂) (f : ModularForm Γ(1) k₁) (z : ℍ),
      (heq ▸ f : ModularForm Γ(1) k₂) z = f z := by intros; subst_vars; rfl
    exact this hcast _ z
  rw [hq_eq]
  have hmul_coe : (↑(GradedMonoid.GMul.mul (D 12) (S (↑(n-12)))) : ℍ → ℂ) =
      ↑((D 12).mul (S (↑(n-12)))) := rfl
  rw [hmul_coe]
  have hmul_coeff := qExpansion_mul_coeff 1 12 (↑(n-12)) (D 12) (S (↑(n-12)))
  simp only [Nat.cast_one] at hmul_coeff; rw [hmul_coeff]
  simp only [PowerSeries.coeff_mul, Finset.antidiagonal_zero, Finset.sum_singleton]
  have hD12 : D 12 = ModForm_mk Γ(1) 12 Delta := by
    change (evalE₄E₆ Delta_poly) 12 = _
    have hev : evalE₄E₆ Delta_poly =
        DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 12 (ModForm_mk Γ(1) 12 Delta) := by
      rw [evalE₄E₆_Delta_poly]; ext i; by_cases hi : i = 12
      · subst hi; simp only [DirectSum.smul_apply, DirectSum.sub_apply, DirectSum.of_eq_same]
        rw [show ModForm_mk Γ(1) 12 Delta = ModForm_mk Γ(1) 12 Delta_E4_E6_aux from by
          rw [Delta_E4_eqn], Delta_E4_E6_eq]; simp only [DirectSum.sub_apply]
      · simp only [DirectSum.smul_apply, DirectSum.sub_apply, DirectSum.of_eq_of_ne _ _ _ hi]
        have he4 : ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ 3) i = 0 := by
          rw [pow_three, DirectSum.of_mul_of, DirectSum.of_mul_of]
          exact DirectSum.of_eq_of_ne _ _ _ (by omega)
        have he6 : ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ 2) i = 0 := by
          rw [pow_two, DirectSum.of_mul_of]; exact DirectSum.of_eq_of_ne _ _ _ (by omega)
        rw [he4, he6, sub_self, smul_zero]
    rw [hev, DirectSum.of_eq_same]
  have hDelta_coeff : (qExpansion 1 ↑(D 12)).coeff 0 = 0 := by
    rw [hD12]
    have hcusp : IsCuspForm Γ(1) 12 (ModForm_mk Γ(1) 12 Delta) := by
      rw [IsCuspForm, CuspFormSubmodule, LinearMap.mem_range]; exact ⟨Delta, rfl⟩
    exact (IsCuspForm_iff_coeffZero_eq_zero 12 _).mp hcusp
  rw [hDelta_coeff, zero_mul]

private lemma coeff_zero_of_eval_zero {n : ℕ} (hn12 : 12 ≤ n)
    (r s : MvPolynomial (Fin 2) ℂ)
    (hr : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight r n)
    (hs : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight s (n - 12))
    (hr_red : ∀ d ∈ r.support, d 0 < 3)
    (heval : (evalE₄E₆ (r + Delta_poly * s)) (↑n : ℤ) = 0) :
    r = 0 := by
  by_cases hr_empty : r.support = ∅
  · rwa [MvPolynomial.support_eq_empty] at hr_empty
  · obtain ⟨d₀, hd₀⟩ := Finset.nonempty_of_ne_empty hr_empty
    have huniq := reduced_poly_is_scalar hn12 r hr hr_red
    have hr_mono : r = MvPolynomial.monomial d₀ (MvPolynomial.coeff d₀ r) := by
      ext d
      by_cases hd : d = d₀
      · subst hd; simp
      · rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hd)]
        by_cases hd_supp : d ∈ r.support
        · exact absurd (huniq d d₀ hd_supp hd₀) hd
        · rwa [MvPolynomial.mem_support_iff, not_not] at hd_supp
    have hwd₀ := hr (MvPolynomial.mem_support_iff.mp hd₀)
    have hwd₀' := weight_eq_4a_6b d₀; rw [hwd₀] at hwd₀'
    set c := MvPolynomial.coeff d₀ r
    suffices hc : c = 0 by rw [hr_mono, hc, MvPolynomial.monomial_zero]
    set Q := qExpansionAddHom (show (0 : ℝ) < (1 : ℝ) by norm_num)
      (show (1 : ℝ) ∈ Γ(1).strictPeriods from by simp) (↑n)
    have hQ_zero : Q ((evalE₄E₆ (r + Delta_poly * s)) (↑n : ℤ)) = 0 := by
      rw [heval]; exact map_zero Q
    rw [show evalE₄E₆ (r + Delta_poly * s) = evalE₄E₆ r + evalE₄E₆ (Delta_poly * s)
      from map_add _ _ _, DFinsupp.add_apply, map_add] at hQ_zero
    have hcoeff_sum : (Q ((evalE₄E₆ r) (↑n : ℤ))).coeff 0 +
        (Q ((evalE₄E₆ (Delta_poly * s)) (↑n : ℤ))).coeff 0 = 0 := by
      rw [← PowerSeries.coeff_add, hQ_zero, map_zero]
    change (qExpansion 1 ↑((evalE₄E₆ r) (↑n : ℤ))).coeff 0 +
      (qExpansion 1 ↑((evalE₄E₆ (Delta_poly * s)) (↑n : ℤ))).coeff 0 = 0 at hcoeff_sum
    set mo := ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ d₀ 0 *
      (DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ d₀ 1)
    have hmo_coeff : (qExpansion 1 ↑(mo (↑n : ℤ))).coeff 0 = 1 :=
      monomial_coeff_zero_eq_one n (d₀ 0) (d₀ 1) (by omega)
    have hq_r : (qExpansion 1 ↑((evalE₄E₆ r) (↑n : ℤ))).coeff 0 = c := by
      rw [hr_mono, monomial_fin2_eq,
        show MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ d₀ 0 *
          MvPolynomial.X (1 : Fin 2) ^ d₀ 1 =
          MvPolynomial.C c * (MvPolynomial.X (0 : Fin 2) ^ d₀ 0 *
          MvPolynomial.X (1 : Fin 2) ^ d₀ 1) from mul_assoc _ _ _,
        map_mul, evalE₄E₆_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1]
      rw [DirectSum.smul_apply]
      have hqs := qExpansion_smul (show (0 : ℝ) < 1 from by norm_num)
        (show (1 : ℝ) ∈ Γ(1).strictPeriods from by simp) c (mo (↑n : ℤ))
      have hcoe : (↑(c • mo (↑n : ℤ)) : ℍ → ℂ) = c • ↑(mo (↑n : ℤ)) := rfl
      rw [hcoe, hqs, PowerSeries.coeff_smul, hmo_coeff, smul_eq_mul, mul_one]
    have hq_ds : (qExpansion 1 ↑((evalE₄E₆ (Delta_poly * s)) (↑n : ℤ))).coeff 0 = 0 :=
      evalE₄E₆_Delta_mul_coeff_zero hn12 s hs
    rw [hq_r, hq_ds, add_zero] at hcoeff_sum; exact hcoeff_sum

private lemma eval_Delta_mul_zero_imp {n : ℕ} (hn12 : 12 ≤ n)
    (s : MvPolynomial (Fin 2) ℂ)
    (hs : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight s (n - 12))
    (hds : (evalE₄E₆ (Delta_poly * s)) (↑n : ℤ) = 0) :
    (evalE₄E₆ s) (↑(n - 12) : ℤ) = 0 := by
  rw [map_mul] at hds
  have hD_grade := evalE₄E₆_whc_grade 12 Delta_poly Delta_poly_isWeightedHomogeneous
  have hS_grade := evalE₄E₆_whc_grade (n - 12) s hs
  set D := evalE₄E₆ Delta_poly
  set S := evalE₄E₆ s
  have hD_single : D = DirectSum.of _ 12 (D 12) := by
    ext k; by_cases hk : k = 12
    · subst hk; simp [DirectSum.of_eq_same]
    · rw [hD_grade k hk, DirectSum.of_eq_of_ne _ _ _ hk]
  have hS_single : S = DirectSum.of _ (↑(n-12) : ℤ) (S (↑(n-12))) := by
    ext k; by_cases hk : k = (↑(n-12) : ℤ)
    · subst hk; simp [DirectSum.of_eq_same]
    · rw [hS_grade k hk, DirectSum.of_eq_of_ne _ _ _ hk]
  rw [hD_single, hS_single, DirectSum.of_mul_of] at hds
  have hcast : (12 : ℤ) + ↑(n - 12) = ↑n := by omega
  have hds2 : GradedMonoid.GMul.mul (D 12) (S (↑(n-12))) = 0 := by
    have h := hds
    rw [DirectSum.of_apply, dif_pos hcast] at h
    have : ∀ {k₁ k₂ : ℤ} (h : k₁ = k₂) (f : ModularForm Γ(1) k₁),
      h ▸ f = (0 : ModularForm Γ(1) k₂) → f = 0 := by
      intros k₁ k₂ heq f hf; cases heq; exact hf
    exact this hcast _ h
  have hD12 : D 12 = ModForm_mk Γ(1) 12 Delta := by
    change (evalE₄E₆ Delta_poly) 12 = _
    have hev : evalE₄E₆ Delta_poly =
        DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 12 (ModForm_mk Γ(1) 12 Delta) := by
      rw [evalE₄E₆_Delta_poly]; ext i; by_cases hi : i = 12
      · subst hi; simp only [DirectSum.smul_apply, DirectSum.sub_apply, DirectSum.of_eq_same]
        rw [show ModForm_mk Γ(1) 12 Delta = ModForm_mk Γ(1) 12 Delta_E4_E6_aux from by
          rw [Delta_E4_eqn], Delta_E4_E6_eq]; simp only [DirectSum.sub_apply]
      · simp only [DirectSum.smul_apply, DirectSum.sub_apply, DirectSum.of_eq_of_ne _ _ _ hi]
        have he4 : ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ 3) i = 0 := by
          rw [pow_three, DirectSum.of_mul_of, DirectSum.of_mul_of]
          exact DirectSum.of_eq_of_ne _ _ _ (by omega)
        have he6 : ((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ 2) i = 0 := by
          rw [pow_two, DirectSum.of_mul_of]; exact DirectSum.of_eq_of_ne _ _ _ (by omega)
        rw [he4, he6, sub_self, smul_zero]
    rw [hev, DirectSum.of_eq_same]
  ext z; simp only [ModularForm.zero_apply]
  have hpw := congr_fun (congr_arg (fun (f : ModularForm Γ(1) _) => f.toFun) hds2) z
  simp only [SlashInvariantForm.toFun_eq_coe, ModularForm.toSlashInvariantForm_coe,
    ModularForm.zero_apply] at hpw
  change (D 12) z * (S (↑(n-12))) z = 0 at hpw
  have hDnz : (D 12) z ≠ 0 := by rw [hD12]; exact Δ_ne_zero z
  exact (mul_eq_zero.mp hpw).resolve_left hDnz

private lemma div_Delta_poly {n : ℕ} (hn12 : 12 ≤ n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0) :
    ∃ q : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight q (n - 12) ∧
      p = Delta_poly * q ∧
      (evalE₄E₆ q) (↑(n - 12) : ℤ) = 0 := by
  obtain ⟨r, s, hr_wh, hs_wh, hp_eq, hr_red⟩ := whomog_poly_Delta_decomp hn12 p hp
  have heval' : (evalE₄E₆ (r + Delta_poly * s)) (↑n : ℤ) = 0 := by rwa [← hp_eq]
  have hr_zero := coeff_zero_of_eval_zero hn12 r s hr_wh hs_wh hr_red heval'
  have hp_ds : p = Delta_poly * s := by rw [hp_eq, hr_zero, zero_add]
  have hds : (evalE₄E₆ (Delta_poly * s)) (↑n : ℤ) = 0 := by rwa [← hp_ds]
  exact ⟨s, hs_wh, hp_ds, eval_Delta_mul_zero_imp hn12 s hs_wh hds⟩

private lemma per_weight_injective_inductive_step (n : ℕ)
    (ih : ∀ m < n, ∀ (p : MvPolynomial (Fin 2) ℂ),
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p m → (evalE₄E₆ p) (↑m : ℤ) = 0 → p = 0)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0)
    (_hk_odd : Even n) (hn12 : 12 ≤ n) : p = 0 := by
  obtain ⟨q, hq_wh, hpq, hq_eval⟩ := div_Delta_poly hn12 p hp heval
  have hq_zero : q = 0 := ih (n - 12) (by omega) q hq_wh hq_eval
  rw [hpq, hq_zero, mul_zero]

private lemma per_weight_injective : ∀ (n : ℕ) (p : MvPolynomial (Fin 2) ℂ),
    MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p n →
    (evalE₄E₆ p) (↑n : ℤ) = 0 → p = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hp heval
  by_cases hk_odd : Odd n
  · exact whomog_eq_zero_of_no_monomials p hp (fun d => no_wt_monomial_of_odd hk_odd d)
  · rw [Nat.not_odd_iff_even] at hk_odd
    by_cases hn4 : n < 4
    · have hn02 : n = 0 ∨ n = 2 := by
        obtain ⟨m, rfl⟩ := hk_odd; omega
      rcases hn02 with rfl | rfl
      · have hpc : p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
          ext d'
          simp only [MvPolynomial.coeff_C]
          by_cases hd' : 0 = d'
          · simp [hd']
          · rw [if_neg hd']
            have : Finsupp.weight E₄E₆Weight d' ≠ 0 := by
              intro hw; apply hd'
              have h46' := weight_eq_4a_6b d'
              rw [hw] at h46'
              symm; ext i; fin_cases i <;> simp [Finsupp.coe_zero] <;> omega
            exact hp.coeff_eq_zero d' this
        rw [hpc] at heval ⊢
        rw [evalE₄E₆_C, Algebra.algebraMap_eq_smul_one] at heval
        have h1eq : (1 : DirectSum ℤ (fun k => ModularForm Γ(1) k)) ((0 : ℕ) : ℤ) =
            (1 : ModularForm Γ(1) 0) := by
          change (1 : DirectSum ℤ (fun k => ModularForm Γ(1) k)) (0 : ℤ) = 1
          have := DirectSum.of_zero_one (fun k : ℤ => ModularForm Γ(1) k)
          conv_lhs => rw [← this]
          exact DirectSum.of_eq_same _ _
        simp only [DirectSum.smul_apply] at heval
        rw [h1eq] at heval
        have h1ne : (1 : ModularForm Γ(1) 0) ≠ 0 := by
          intro h
          have := congr_fun (congr_arg (fun x => x.toFun) h) UpperHalfPlane.I
          simp [ModularForm.one_coe_eq_one] at this
        rcases smul_eq_zero.mp heval with hc | h1z
        · rw [hc, map_zero]
        · exact absurd h1z h1ne
      · exact whomog_eq_zero_of_no_monomials p hp (fun d => no_wt_monomial_of_two d)
    · push_neg at hn4
      by_cases hn12 : n < 12
      · have hn_cases : n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 := by
          obtain ⟨m, rfl⟩ := hk_odd; omega
        rcases hn_cases with rfl | rfl | rfl | rfl
        · obtain ⟨d₀, hd0a, hd0b⟩ := finsupp_of_fin2 1 0
          apply per_weight_injective_unique_monomial p hp heval d₀
            (by rw [weight_eq_4a_6b]; omega)
          · intro d hd; have h46 := weight_eq_4a_6b d; rw [hd] at h46
            have hda : d 0 = d₀ 0 := by omega
            have hdb : d 1 = d₀ 1 := by omega
            ext i; fin_cases i <;> assumption
          · rw [hd0a, hd0b]
            intro habs
            have := monomial_coeff_zero_eq_one 4 1 0 (by omega)
            rw [habs] at this; simp [qExpansion_zero] at this
        · obtain ⟨d₀, hd0a, hd0b⟩ := finsupp_of_fin2 0 1
          apply per_weight_injective_unique_monomial p hp heval d₀
            (by rw [weight_eq_4a_6b]; omega)
          · intro d hd; have h46 := weight_eq_4a_6b d; rw [hd] at h46
            have hda : d 0 = d₀ 0 := by omega
            have hdb : d 1 = d₀ 1 := by omega
            ext i; fin_cases i <;> assumption
          · rw [hd0a, hd0b]
            intro habs
            have := monomial_coeff_zero_eq_one 6 0 1 (by omega)
            rw [habs] at this; simp [qExpansion_zero] at this
        · obtain ⟨d₀, hd0a, hd0b⟩ := finsupp_of_fin2 2 0
          apply per_weight_injective_unique_monomial p hp heval d₀
            (by rw [weight_eq_4a_6b]; omega)
          · intro d hd; have h46 := weight_eq_4a_6b d; rw [hd] at h46
            have hda : d 0 = d₀ 0 := by omega
            have hdb : d 1 = d₀ 1 := by omega
            ext i; fin_cases i <;> assumption
          · rw [hd0a, hd0b]
            intro habs
            have := monomial_coeff_zero_eq_one 8 2 0 (by omega)
            rw [habs] at this; simp [qExpansion_zero] at this
        · obtain ⟨d₀, hd0a, hd0b⟩ := finsupp_of_fin2 1 1
          apply per_weight_injective_unique_monomial p hp heval d₀
            (by rw [weight_eq_4a_6b]; omega)
          · intro d hd; have h46 := weight_eq_4a_6b d; rw [hd] at h46
            have hda : d 0 = d₀ 0 := by omega
            have hdb : d 1 = d₀ 1 := by omega
            ext i; fin_cases i <;> assumption
          · rw [hd0a, hd0b]
            intro habs
            have := monomial_coeff_zero_eq_one 10 1 1 (by omega)
            rw [habs] at this; simp [qExpansion_zero] at this
      · push_neg at hn12
        exact per_weight_injective_inductive_step n ih p hp heval hk_odd hn12

/-- The evaluation homomorphism `evalE₄E₆` is injective (E₄ and E₆ are algebraically independent). -/
theorem evalE₄E₆_injective : Function.Injective evalE₄E₆ := by
  intro p q hpq
  rw [← sub_eq_zero]
  set r := p - q with hr_def
  have hr : evalE₄E₆ r = 0 := by rw [map_sub, sub_eq_zero]; exact hpq
  rw [← MvPolynomial.sum_weightedHomogeneousComponent E₄E₆Weight r]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  exact per_weight_injective n _
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    (by rw [evalE₄E₆_component_eq]; rw [hr]; rfl)

/-! ## Main isomorphism and corollaries -/

/-- The graded ring of level 1 modular forms is isomorphic to the weighted polynomial ring in E₄ and E₆. -/
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
