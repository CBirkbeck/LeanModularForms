module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Cases

@[expose] public section

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

theorem upper_ne_int (x : ℍ) (d : ℤ) : (x : ℂ) + d ≠ 0 := by
  intro h
  have h1 : 0 < (x : ℂ).im := by simpa using im_pos x
  rw [add_eq_zero_iff_eq_neg.mp h] at h1
  simp at h1

theorem aut_iter_deriv (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ ↦ 1 / (z + d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ ↦ (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  induction k generalizing x with
  | zero => simp
  | succ k IH =>
    rw [iteratedDerivWithin_succ]
    simp only [one_div, Nat.cast_succ, Nat.factorial, Nat.cast_mul]
    have H : derivWithin (fun (z : ℂ) ↦ (-1: ℂ) ^ k * ↑k ! * ((z + ↑d) ^ (k + 1))⁻¹)
               {z : ℂ | 0 < z.im} x =
             (-1) ^ (↑k + 1) * ((↑k + 1) * ↑k !) * ((x + ↑d) ^ (↑k + 1 + 1))⁻¹ := by
      rw [DifferentiableAt.derivWithin]
      · simp only [deriv_const_mul_field']
        rw [show (fun z : ℂ ↦ ((z + d) ^ (k + 1))⁻¹) =
              (fun z : ℂ ↦ (z + d) ^ (k + 1))⁻¹ from rfl,
            show (fun z : ℂ ↦ ((z + d) ^ (k + 1))) =
              (fun z : ℂ ↦ (z + d)) ^ (k + 1) from rfl,
            deriv_inv'', deriv_pow, deriv_add_const', deriv_id'']
        · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, mul_one]
          rw [pow_add]
          simp [pow_one]
          have Hw : (-(((k : ℂ) + 1) * (x + ↑d) ^ k) / ((x + ↑d) ^ k * (x + ↑d)) ^ 2) =
                    -(↑k + 1) / (x + ↑d) ^ (k + 2) := by
            rw [div_eq_div_iff]
            · ring
            · exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero k (upper_ne_int ⟨x, hx⟩ d))
                (upper_ne_int ⟨x, hx⟩ d))
            · exact pow_ne_zero (k + 2) (upper_ne_int ⟨x, hx⟩ d)
          rw [Hw]; ring
        · fun_prop
        · fun_prop
        exact pow_ne_zero (k + 1) (upper_ne_int ⟨x, hx⟩ d)
      · exact DifferentiableAt.mul (by fun_prop)
          (DifferentiableAt.inv (by fun_prop) (pow_ne_zero (k + 1) (upper_ne_int ⟨x, hx⟩ d)))
      · exact (isOpen_lt (by fun_prop) (by fun_prop)).uniqueDiffWithinAt hx
    rw [← H]
    refine derivWithin_congr (fun r hr ↦ ?_) (by simpa using IH hx)
    simpa using IH hr

theorem aut_iter_deriv' (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ ↦ 1 / (z - d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ ↦ (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  simpa [sub_eq_add_neg] using aut_iter_deriv (-d : ℤ) k hx

theorem aut_contDiffOn (d : ℤ) (k : ℕ) :
    ContDiffOn ℂ k (fun z : ℂ ↦ 1 / (z - d)) {z : ℂ | 0 < z.im} := by
  simp only [one_div]
  refine ContDiffOn.inv (by fun_prop) fun x hx ↦ ?_
  have := upper_ne_int ⟨x, hx⟩ (-d)
  simpa [sub_eq_add_neg] using this

theorem iter_div_aut_add (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ ↦ 1 / (z - d) + 1 / (z + d)) {z : ℂ | 0 < z.im})
      ((fun t : ℂ ↦ (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) + fun t : ℂ ↦
        (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  show iteratedDerivWithin k ((fun z : ℂ ↦ 1 / (z - d)) + fun z : ℂ ↦ 1 / (z + d)) _ x = _
  rw [iteratedDerivWithin_add hx
    ((IsOpen.uniqueDiffOn (isOpen_lt (by fun_prop) (by fun_prop)))) (aut_contDiffOn d k x hx)
    (by simpa [sub_eq_add_neg] using aut_contDiffOn (-d) k x hx),
    aut_iter_deriv d k hx, aut_iter_deriv' d k hx]
  rfl

theorem exp_iter_deriv_within (n m : ℕ) :
    EqOn (iteratedDerivWithin n (fun s : ℂ ↦ Complex.exp (2 * ↑π * Complex.I * m * s))
           {z : ℂ | 0 < z.im})
      (fun t ↦ (2 * ↑π * Complex.I * m) ^ n * Complex.exp (2 * ↑π * Complex.I * m * t))
      {z : ℂ | 0 < z.im} := by
  refine EqOn.trans (iteratedDerivWithin_of_isOpen (isOpen_lt (by fun_prop) (by fun_prop))) ?_
  intro x _
  exact congr_fun (iteratedDeriv_cexp_const_mul ..) x
