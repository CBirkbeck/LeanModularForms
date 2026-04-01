module

public import LeanModularForms.Modularforms.Generators.Defs

/-!
# Generators of the graded ring of level 1 modular forms: Surjectivity

We prove that `evalE₄E₆` is surjective by showing each `DirectSum.of _ k f` lies in
its range (strong induction on weight), then using the subalgebra closure of the range.
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

private lemma mul_modform_ne_zero_of_coeff_one {k₁ k₂ : ℤ}
    (f : ModularForm Γ(1) k₁) (g : ModularForm Γ(1) k₂)
    (hf : (qExpansion 1 f).coeff 0 = 1) (hg : (qExpansion 1 g).coeff 0 = 1) :
    (f.mul g : ModularForm Γ(1) (k₁ + k₂)) ≠ 0 := by
  intro h
  have hcoeff : (qExpansion 1 (f.mul g)).coeff 0 = 1 := by
    have := qExpansion_mul_coeff 1 k₁ k₂ f g
    simp only [Nat.cast_one] at this; rw [this]
    simp only [PowerSeries.coeff_mul, Finset.antidiagonal_zero, Finset.sum_singleton, hf, hg,
      mul_one]
  have hcoe : (⇑(f.mul g) : ℍ → ℂ) = 0 := by
    rw [h]; ext z; simp only [zero_apply, Pi.zero_apply]
  rw [show qExpansion 1 (f.mul g) = qExpansion 1 (0 : ℍ → ℂ) from
    congr_arg (qExpansion 1) hcoe, qExpansion_zero] at hcoeff
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_zero,
    zero_ne_one] at hcoeff

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
    g = mul_Delta_map ↑n
      (CuspForms_iso_Modforms ↑n (IsCuspForm_to_CuspForm Γ(1) ↑n g hg)) := by
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

lemma monomial_coeff_zero_eq_one (n a b : ℕ) (hab : 4 * a + 6 * b = n) :
    (qExpansion 1
      (((DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄) ^ a *
        (DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆) ^ b)
        (↑n : ℤ))).coeff 0 = 1 := by
  subst hab
  have hab' : (↑(4 * a + 6 * b) : ℤ) = ↑a * 4 + ↑b * 6 := by push_cast; ring
  rw [hab', DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
  convert_to (qExpansion 1 (⇑(GradedMonoid.GMul.mul (GradedMonoid.GMonoid.gnpow a E₄)
      (GradedMonoid.GMonoid.gnpow b E₆)))).coeff 0 = 1 using 2
  · simp only [Int.nsmul_eq_mul, DirectSum.of_eq_same]
  change (qExpansion 1 (⇑((GradedMonoid.GMonoid.gnpow a E₄).mul
      (GradedMonoid.GMonoid.gnpow b E₆)))).coeff 0 = 1
  have hqm := qExpansion_mul_coeff 1 (a • (4 : ℤ)) (b • (6 : ℤ))
      (GradedMonoid.GMonoid.gnpow a E₄) (GradedMonoid.GMonoid.gnpow b E₆)
  simp only [Nat.cast_one] at hqm
  rw [hqm]
  have hgnpow4 : (GradedMonoid.GMonoid.gnpow a E₄ : ModularForm Γ(1) (a • 4)) =
      ((DirectSum.of _ 4 E₄) ^ a) (a • (4 : ℤ)) := by
    rw [DirectSum.ofPow]; simp only [Int.nsmul_eq_mul, DirectSum.of_eq_same]
  have hgnpow6 : (GradedMonoid.GMonoid.gnpow b E₆ : ModularForm Γ(1) (b • 6)) =
      ((DirectSum.of _ 6 E₆) ^ b) (b • (6 : ℤ)) := by
    rw [DirectSum.ofPow]; simp only [Int.nsmul_eq_mul, DirectSum.of_eq_same]
  simp_rw [hgnpow4, hgnpow6]
  change (qExpansion 1 ⇑(((DirectSum.of _ 4 E₄) ^ a) (↑a * 4)) *
       qExpansion 1 ⇑(((DirectSum.of _ 6 E₆) ^ b) (↑b * 6))).coeff 0 = 1
  rw [qExpansion_pow, qExpansion_pow]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow]
  have hc4 : PowerSeries.constantCoeff (qExpansion 1 (⇑E₄)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact E4_q_exp_zero
  have hc6 : PowerSeries.constantCoeff (qExpansion 1 (⇑E₆)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact E6_q_exp_zero
  simp only [hc4, one_pow, hc6, mul_one]

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
            simp only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, one_coe_eq_one,
              Pi.one_apply, zero_apply, one_ne_zero] at this
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
            rw [map_mul, map_mul, evalE₄E₆_C, evalE₄E₆_X0, evalE₄E₆_X1,
              DirectSum.of_mul_of,
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
          have hsp : (1 : ℝ) ∈ Γ(1).strictPeriods := by
            simp only [CongruenceSubgroup.strictPeriods_Gamma, Nat.cast_one,
              AddSubgroup.mem_zmultiples]
          set Q := qExpansionAddHom (by norm_num : (0 : ℝ) < 1) hsp (↑n)
          have hQ_smul : Q (c • mn) = c • Q mn :=
            qExpansion_smul (by norm_num : (0 : ℝ) < 1) hsp c mn
          change (Q (f - c • mn)).coeff 0 = 0
          rw [map_sub, hQ_smul, show Q f = qExpansion 1 f from rfl,
            show Q mn = qExpansion 1 mn from rfl, map_sub, map_smul, smul_eq_mul, hmn_coeff,
            mul_one, sub_self]
        set g := f - c • mn
        have hcast : (↑n : ℤ) - 12 = (↑(n - 12) : ℤ) := by omega
        set h' := CuspForms_iso_Modforms ↑n (IsCuspForm_to_CuspForm Γ(1) ↑n g hg_cusp)
        have hg_ds : DirectSum.of _ (↑n : ℤ) g =
            DirectSum.of _ ((↑n : ℤ) - 12) h' *
            DirectSum.of _ 12 (ModForm_mk Γ(1) 12 Delta) := by
          rw [cuspform_eq_mul_Delta n (by omega) g hg_cusp]
          exact mul_Delta_map_eq_DirectSum_mul n (by omega) h'
        have hof_cast : DirectSum.of _ ((↑n : ℤ) - 12) h' =
            DirectSum.of _ (↑(n - 12) : ℤ) (hcast ▸ h') := by
          have : ∀ (k1 k2 : ℤ) (hk : k1 = k2) (x : ModularForm Γ(1) k1),
            DirectSum.of _ k1 x = DirectSum.of _ k2 (hk ▸ x) := by
            intros k1 k2 hk x; subst hk; rfl
          exact this _ _ hcast h'
        have hih : DirectSum.of _ ((↑n : ℤ) - 12) h' ∈ Set.range evalE₄E₆ := by
          rw [hof_cast]; exact ih (n - 12) (by omega) (by omega) (hcast ▸ h')
        have hg_in : DirectSum.of _ (↑n : ℤ) g ∈ Set.range evalE₄E₆ := by
          rw [hg_ds]
          obtain ⟨p1, hp1⟩ := hih
          obtain ⟨p2, hp2⟩ := delta_mem_range_evalE₄E₆
          exact ⟨p1 * p2, by rw [map_mul, hp1, hp2]⟩
        have hmn_in : mo ∈ Set.range evalE₄E₆ :=
          ⟨MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b, by
            rw [map_mul, map_pow, map_pow, evalE₄E₆_X0, evalE₄E₆_X1]⟩
        have hmn_eq : DirectSum.of _ (↑n : ℤ) mn = mo := by
          simp only [mn, mo]
          rw [DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
          have hk' : a • (4 : ℤ) + b • (6 : ℤ) = ↑n := by
            simp only [Int.nsmul_eq_mul]; linarith
          rw [show (↑n : ℤ) = a • (4 : ℤ) + b • (6 : ℤ) from hk'.symm,
            DirectSum.of_eq_same]
        have hf_eq : f = g + c • mn := by simp only [g, sub_add_cancel]
        have hf_ds : DirectSum.of _ (↑n : ℤ) f =
            DirectSum.of _ (↑n : ℤ) g + c • DirectSum.of _ (↑n : ℤ) mn := by
          rw [hf_eq, map_add, ← DirectSum.of_smul]
        rw [hf_ds, hmn_eq]
        obtain ⟨p1, hp1⟩ := hg_in
        obtain ⟨p2, hp2⟩ := hmn_in
        exact ⟨p1 + MvPolynomial.C c * p2, by
          rw [map_add, hp1, map_mul, evalE₄E₆_C, hp2,
            Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]⟩

/-- The evaluation homomorphism `evalE₄E₆ : ℂ[X₀, X₁] →ₐ[ℂ] ⨁_k M_k(Γ(1))`
is surjective. -/
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
