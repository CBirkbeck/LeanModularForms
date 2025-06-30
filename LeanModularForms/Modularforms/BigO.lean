import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence



open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical


lemma norm_symm (x y : ℤ) : ‖![x, y]‖ = ‖![y,x]‖ := by
  simp_rw [EisensteinSeries.norm_eq_max_natAbs]
  rw [max_comm]
  simp


lemma linear_bigO (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹)  := by
  have :=  Asymptotics.IsBigO.abs_right (EisensteinSeries.linear_inv_isBigO_right m z)
  simp_rw [← abs_inv]
  apply this

lemma linear_bigO_pow (m : ℤ) (z : ℍ) (k : ℕ) : (fun (n : ℤ) => ((((m : ℂ) * z + n)) ^ k )⁻¹) =O[cofinite]
    fun n => ((|(n : ℝ)| ^ k)⁻¹)  := by
  simp_rw [← inv_pow]
  apply Asymptotics.IsBigO.pow
  apply linear_bigO m z


lemma Asymptotics.IsBigO.zify {α β: Type*} [Norm α] [Norm β] {f : ℤ → α} {g : ℤ → β} (hf : f =O[cofinite] g) :
    (fun (n : ℕ) => f n) =O[cofinite] fun n => g n := by
  rw [@isBigO_iff] at *
  obtain ⟨C, hC⟩ := hf
  use C
  rw [Int.cofinite_eq] at hC
  rw [Nat.cofinite_eq_atTop]
  apply Filter.Eventually.natCast_atTop  (p := fun n => ‖f n‖ ≤ C * ‖g n‖)
  simp_all only [eventually_sup, eventually_atBot, eventually_atTop, ge_iff_le]


lemma Asymptotics.IsBigO.of_neg {α β: Type*} [Norm α] [Norm β] {f : ℤ → α} {g : ℤ → β}
    (hf : f =O[cofinite] g) : (fun n => f (-n)) =O[cofinite] fun n => g (-n) := by
  rw [← Equiv.neg_apply]
  apply Asymptotics.IsBigO.comp_tendsto hf
  refine Injective.tendsto_cofinite (Equiv.injective (Equiv.neg ℤ))


lemma linear_bigO_nat (m : ℤ) (z : ℍ) : (fun (n : ℕ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹)  := by
  have := linear_bigO (m : ℤ) z
  apply this.zify




lemma linear_bigO' (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((n : ℂ) * z + m)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹)  := by
  have hz : (z : ℂ) ≠ 0 := by
    exact ne_zero z
  have :=  Asymptotics.IsBigO.abs_right (EisensteinSeries.linear_inv_isBigO_left m hz)
  simp_rw [← abs_inv]
  apply this
