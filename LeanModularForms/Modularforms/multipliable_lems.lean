module

public import LeanModularForms.Modularforms.summable_lems

@[expose] public section

/-!
# Multipliability lemmas

This file collects multipliability lemmas used in the construction of the Eta and Delta
products, including a non-vanishing criterion for infinite products of `1 + f i x`.
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction

/-- A summable function `f` produces a multipliable family `1 + f n`. -/
lemma Complex.summable_nat_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f) :
    Multipliable (fun n : ℕ => 1 + f n) := by
  apply Complex.multipliable_of_summable_log
  exact Complex.summable_log_one_add_of_summable hf

theorem term_ne_zero (z : ℍ) (n : ℕ) : 1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have := exp_upperHalfPlane_lt_one_nat z n
  rw [← h] at this
  simp at this

theorem ball_pow_ne_one (x : ℂ) (hx : x ∈ ball 0 1) (n : ℕ) :
    1 + (fun n ↦ -x ^ (n + 1)) n ≠ 0 := by
  simp only [mem_ball, dist_zero_right] at hx
  rw [← sub_eq_add_neg, sub_ne_zero]
  have hxn : ‖x ^ (n + 1)‖ < 1 := by
    simp only [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by omega)
  intro h
  rw [← h] at hxn
  simp at hxn

theorem multipliable_lt_one (x : ℂ) (hx : x ∈ ball 0 1) :
    Multipliable fun i ↦ 1 - x ^ (i + 1) := by
  have := Complex.summable_nat_multipliable_one_add (fun (n : ℕ) => -x ^ (n + 1)) ?_
  · conv => enter [1]; ext n; rw [sub_eq_add_neg]
    exact this
  rw [summable_neg_iff, summable_nat_add_iff, summable_geometric_iff_norm_lt_one]
  simpa using hx

lemma multipliableEtaProductExpansion (z : ℍ) :
    Multipliable (fun (n : ℕ) => 1 - cexp (2 * π * Complex.I * (n + 1) * z)) := by
  have := Complex.summable_nat_multipliable_one_add
    (fun (n : ℕ) => -cexp (2 * π * Complex.I * (n + 1) * z)) ?_
  · simp at this
    refine this.congr (fun n => by ring)
  rw [← summable_norm_iff]
  simpa using summable_exp_pow z

lemma multipliableEtaProductExpansion_pnat (z : ℍ) :
    Multipliable (fun (n : ℕ+) => 1 - cexp (2 * π * Complex.I * n * z)) := by
  conv => enter [1]; ext n; rw [sub_eq_add_neg]
  let g := fun (n : ℕ) => 1 - cexp (2 * π * Complex.I * n * z)
  have := multipliableEtaProductExpansion z
  conv at this =>
    enter [1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
  rw [← multipliable_pnat_iff_multipliable_succ (f := g)] at this
  exact this.congr (fun _ => rfl)

lemma tprod_ne_zero (x : ℍ) (f : ℕ → ℍ → ℂ) (hf : ∀ i x, 1 + f i x ≠ 0)
    (hu : ∀ x : ℍ, Summable fun n => f n x) : (∏' i : ℕ, (1 + f i) x) ≠ 0 := by
  have := Complex.cexp_tsum_eq_tprod (f := fun n => 1 + f n x) (fun n => hf n x)
  simp only [Pi.add_apply, Pi.one_apply]
  rw [← this (Complex.summable_log_one_add_of_summable (hu x))]
  exact exp_ne_zero _

lemma multipliable_pow {ι : Type*} (f : ι → ℂ) (hf : Multipliable f) (n : ℕ) :
    Multipliable (fun i => f i ^ n) := by
  induction n with
  | zero => simp
  | succ n hn =>
    conv => enter [1]; intro u; rw [pow_succ]
    exact hn.mul hf

lemma multipliableDeltaProductExpansion_pnat (z : ℍ) :
    Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z)) ^ 24) :=
  multipliable_pow _ (multipliableEtaProductExpansion_pnat z) 24

lemma tprod_pow (f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) :
    (∏' (i : ℕ), f i) ^ n = ∏' (i : ℕ), f i ^ n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ, hn, ← Multipliable.tprod_mul (multipliable_pow f hf n) hf]
    simp [pow_succ]

variable {a a₁ a₂ : ℝ} {ι : Type*}

theorem hasProd_le_nonneg (f g : ι → ℝ) (h : ∀ i, f i ≤ g i) (h0 : ∀ i, 0 ≤ f i)
    (hf : HasProd f a₁) (hg : HasProd g a₂) : a₁ ≤ a₂ := by
  refine le_of_tendsto_of_tendsto' hf hg fun s => ?_
  exact Finset.prod_le_prod (fun i _ => h0 i) (fun i _ => h i)

theorem HasProd.le_one_nonneg (g : ℕ → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i)
    (ha : HasProd g a) : a ≤ 1 :=
  hasProd_le_nonneg (f := g) (g := fun _ => 1) h h0 ha hasProd_one

theorem one_le_tprod_nonneg (g : ℕ → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i) :
    ∏' i, g i ≤ 1 := by
  by_cases hg : Multipliable g
  · exact hg.hasProd.le_one_nonneg g h h0
  · rw [tprod_eq_one_of_not_multipliable hg]
