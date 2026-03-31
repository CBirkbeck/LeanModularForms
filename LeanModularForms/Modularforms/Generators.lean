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

/-! ## Odd-weight vanishing

For odd weight k, the space `M_k(Γ(1))` is trivial. The key idea is that `-I ∈ SL(2, ℤ)` acts
trivially on `ℍ` but the slash action introduces a factor `(-1)^k`. For odd k this gives
`f = -f`, hence `f = 0`. -/

/-- For odd weight k, every modular form of weight k for Γ(1) is zero.

The proof uses `-I ∈ SL(2, ℤ)`: the slash action of `-I` on weight k gives
`(-1)^k * f(z)` (since `-I` acts trivially on ℍ but `j(-I, z) = -1`).
Modularity forces `f |_k (-I) = f`, so for odd k we get `f = -f`, hence `f = 0`. -/
theorem levelOne_odd_weight_eq_zero {k : ℤ} (hk : Odd k)
    (f : ModularForm (CongruenceSubgroup.Gamma 1) k) : f = 0 := by
  ext z
  -- f |_k (-1) = f by modularity for Γ(1)
  have hmod : (f.toFun ∣[k] (-1 : SL(2, ℤ))) z = f z := by
    have := f.slash_action_eq' _
      (Subgroup.mem_map_of_mem _ (CongruenceSubgroup.mem_Gamma_one (-1)))
    exact congrFun this z
  -- Expand via SL_slash_apply: f((-1)•z) * denom(-1,z)^(-k)
  rw [SL_slash_apply] at hmod
  -- (-1) • z = z
  rw [ModularGroup.SL_neg_smul, one_smul] at hmod
  -- denom(-1, z) = -1, and (-1)^(-k) = -1 for odd k
  have hdenom : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) (-1 : SL(2, ℤ)))) ↑z = -1 := by
    rw [ModularGroup.denom_apply]
    simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  rw [hdenom, zpow_neg, hk.neg_one_zpow, inv_neg, inv_one] at hmod
  -- Now hmod : f.toFun z * -1 = f z; reconcile f.toFun with f
  simp only [SlashInvariantForm.toFun_eq_coe, ModularForm.toSlashInvariantForm_coe] at hmod
  -- f(z) * (-1) = f(z) implies 2 * f(z) = 0, hence f(z) = 0 (char 0)
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
