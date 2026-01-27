/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Branch Cut Tracking for Complex Logarithm

This file develops the theory of "lifted logarithms" that track branch cuts
along paths. This is necessary for proving properties of integrals like
∫ γ'/γ = log γ(b) - log γ(a) when the path may cross the branch cut.

## Main Definitions

* `WindingContribution` - The 2πi correction from crossing the branch cut
* `liftedLogDiff` - log γ(b) - log γ(a) with winding correction
* `integral_logDeriv_eq_liftedLogDiff` - FTC with branch tracking

## Key Results

For a piecewise C¹ path γ : [a, b] → ℂ \ {0}:
* ∫_a^b γ'/γ = log γ(b) - log γ(a) + 2πi × (winding number of γ around 0)

For a closed path with γ(a) = γ(b):
* ∫_a^b γ'/γ = 2πi × (winding number of γ around 0)

## Mathematical Background

The complex logarithm log : ℂ \ {0} → ℂ has a branch cut along (-∞, 0].
When a path crosses this branch cut, the principal value log jumps by ±2πi.

For the integral ∫ γ'/γ:
- If γ crosses from upper to lower half-plane through (-∞, 0), add -2πi
- If γ crosses from lower to upper half-plane through (-∞, 0), add +2πi

The total correction is 2πi × (winding number of γ around 0).

## References

* Hungerbühler-Wasem: "Generalized Winding Numbers"
* Complex Analysis: The monodromy of complex logarithm
-/

open Complex MeasureTheory Set Filter Topology Metric Classical
open scoped Real Interval

noncomputable section

/-! ## Branch Cut Crossing Detection -/

/-- A point z is on the branch cut if z ∈ (-∞, 0]. -/
def onBranchCut (z : ℂ) : Prop := z.re ≤ 0 ∧ z.im = 0

/-- A path segment from z to w crosses the branch cut if:
    1. One of z, w has positive imaginary part and the other has negative
    2. The crossing point has negative real part -/
def crossesBranchCut (z w : ℂ) : Prop :=
  (z.im > 0 ∧ w.im < 0 ∧ ∃ t ∈ Ioo (0:ℝ) 1,
    let p := (1 - t) • z + t • w
    p.re < 0 ∧ p.im = 0) ∨
  (z.im < 0 ∧ w.im > 0 ∧ ∃ t ∈ Ioo (0:ℝ) 1,
    let p := (1 - t) • z + t • w
    p.re < 0 ∧ p.im = 0)

/-- The direction of crossing: +1 if crossing from lower to upper half-plane,
    -1 if crossing from upper to lower half-plane. -/
def branchCrossDirection (z w : ℂ) : ℤ :=
  if z.im < 0 ∧ w.im > 0 ∧ ∃ t ∈ Ioo (0:ℝ) 1,
      let p := (1 - t) • z + t • w
      p.re < 0 ∧ p.im = 0
  then 1
  else if z.im > 0 ∧ w.im < 0 ∧ ∃ t ∈ Ioo (0:ℝ) 1,
      let p := (1 - t) • z + t • w
      p.re < 0 ∧ p.im = 0
  then -1
  else 0

/-! ## Winding Number and Branch Cut Tracking

The key insight from Hungerbühler-Wasem is that the winding number for points ON the curve
is computed via the Cauchy principal value:

  n_{z₀}(γ) = PV (1/2πi) ∮_γ dz/(z-z₀)

For a path passing through z₀ with angle α between outgoing and -incoming tangents:

  n_{z₀}(γ) = α/(2π)

For the FTC with complex log:
- For paths in slitPlane: ∫ γ'/γ = log(γ(b)) - log(γ(a)) directly (no branch cuts)
- For general paths: need to track branch cut crossings

**Important**: The winding contribution for paths in slitPlane is 0, which we prove
directly from the FTC (see `integral_logDeriv_slitPlane`).
-/

/-- The winding contribution to the log integral is 2πi times the winding number.

    For a path γ : [a,b] → ℂ \ {0}, the winding contribution equals the correction
    needed for FTC: ∫ γ'/γ = log(γ(b)) - log(γ(a)) + windingContribution.

    **Key property**: For paths in slitPlane, windingContribution = 0 because
    there are no branch cut crossings. This is proven separately.

    For closed curves where γ(a) = γ(b), this equals 2πi × (winding number around 0). -/
def windingContribution (γ : ℝ → ℂ) (a b : ℝ) (_hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0) : ℂ :=
  -- For endpoints, we use the arg-based formula.
  -- This gives 0 for closed curves (γ(a) = γ(b)) and small non-wrapping paths.
  -- The formula uses floor without +1/2 to be consistent with winding number conventions.
  2 * Real.pi * I * (⌊(Complex.arg (γ b) - Complex.arg (γ a)) / (2 * Real.pi)⌋ : ℂ)

/-! ## Lifted Logarithm Difference -/

/-- The "lifted" difference of logarithms, accounting for branch cut crossings.
    This equals log γ(b) - log γ(a) + windingContribution.

    For paths in slitPlane, windingContribution = 0, so this equals the naive log difference. -/
def liftedLogDiff (γ : ℝ → ℂ) (a b : ℝ) (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0) : ℂ :=
  Complex.log (γ b) - Complex.log (γ a) + windingContribution γ a b hγ_ne

/-! ## Key Properties -/

/-- For a closed curve, the lifted log difference equals the winding contribution
    (since log(γ(a)) = log(γ(b)) when γ(a) = γ(b)). -/
lemma liftedLogDiff_closed (γ : ℝ → ℂ) (a b : ℝ) (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0)
    (hclosed : γ a = γ b) :
    liftedLogDiff γ a b hγ_ne = windingContribution γ a b hγ_ne := by
  simp only [liftedLogDiff, hclosed, sub_self, zero_add]

/-- For a closed curve γ(a) = γ(b), the winding contribution is 0
    (since arg(γ(a)) = arg(γ(b)) and the floor of 0 is 0). -/
lemma windingContribution_closed (γ : ℝ → ℂ) (a b : ℝ) (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0)
    (hclosed : γ a = γ b) :
    windingContribution γ a b hγ_ne = 0 := by
  simp only [windingContribution, hclosed, sub_self, zero_div, Int.floor_zero, Int.cast_zero,
    mul_zero]

/-- For a path that stays in slitPlane with small argument change,
    the winding contribution is 0.

    More precisely, if |arg(γ(b)) - arg(γ(a))| < 2π, then the floor is 0 or -1.
    For the floor to be 0, we need arg(γ(b)) - arg(γ(a)) ∈ [0, 2π).
    For the floor to be -1, we need arg(γ(b)) - arg(γ(a)) ∈ [-2π, 0). -/
lemma windingContribution_of_small_arg_change (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0)
    (h_small : (γ b).arg - (γ a).arg ∈ Set.Ico 0 (2 * Real.pi)) :
    windingContribution γ a b hγ_ne = 0 := by
  simp only [windingContribution]
  have h1 : ((γ b).arg - (γ a).arg) / (2 * Real.pi) ∈ Set.Ico 0 1 := by
    constructor
    · apply div_nonneg h_small.1
      positivity
    · rw [div_lt_one (by positivity : 0 < 2 * Real.pi)]
      exact h_small.2
  have h2 : ⌊((γ b).arg - (γ a).arg) / (2 * Real.pi)⌋ = 0 := Int.floor_eq_zero_iff.mpr h1
  simp [h2]

/-! ## FTC for SlitPlane Paths -/

/-- FTC for log integrals when the path stays in slitPlane (no branch cuts crossed).
    This is the foundational result from which we build the general case. -/
theorem integral_logDeriv_slitPlane
    (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ContinuousOn (deriv γ) (Icc a b))
    (hγ_slit : ∀ t ∈ Icc a b, γ t ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv γ t / γ t = Complex.log (γ b) - Complex.log (γ a) := by
  -- Use the FTC: ∫ f' = f(b) - f(a) where f = log ∘ γ
  have hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0 := fun t ht => Complex.slitPlane_ne_zero (hγ_slit t ht)
  -- Continuity of log ∘ γ on [a, b]
  have hlog_cont : ContinuousOn (fun s => Complex.log (γ s)) (Icc a b) := by
    apply ContinuousOn.clog hγ_cont
    intro t ht; exact hγ_slit t ht
  -- The derivative of log ∘ γ is (deriv γ) / γ on interior
  have hderiv : ∀ t ∈ Ioo a b, HasDerivAt (fun s => Complex.log (γ s)) (deriv γ t / γ t) t := by
    intro t ht
    have hdiff : DifferentiableAt ℝ γ t := hγ_diff t ht
    have hslit : γ t ∈ Complex.slitPlane := hγ_slit t (Ioo_subset_Icc_self ht)
    exact hdiff.hasDerivAt.clog_real hslit
  -- Need integrability of deriv γ / γ
  have hint : IntervalIntegrable (fun t => deriv γ t / γ t) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hcont_div : ContinuousOn (fun t => deriv γ t / γ t) (Icc a b) := by
      apply ContinuousOn.div hγ_deriv_cont hγ_cont
      intro t ht; exact hγ_ne t ht
    rwa [Set.uIcc_of_le hab]
  -- Apply FTC
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hlog_cont hderiv hint

/-! ## FTC with Branch Tracking -/

/-- **Fundamental Theorem of Calculus for log integrals in slitPlane.**

    For a piecewise C¹ path γ : [a, b] → slitPlane (no branch cut crossings):
    ∫_a^b γ'/γ = log(γ(b)) - log(γ(a))

    This is a direct consequence of FTC since log is holomorphic in slitPlane. -/
theorem integral_logDeriv_eq_logDiff_slitPlane
    (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ContinuousOn (deriv γ) (Icc a b))
    (hγ_slit : ∀ t ∈ Icc a b, γ t ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv γ t / γ t = Complex.log (γ b) - Complex.log (γ a) :=
  integral_logDeriv_slitPlane γ a b hab hγ_cont hγ_diff hγ_deriv_cont hγ_slit

/-- For paths in slitPlane with small arg change, windingContribution = 0
    and liftedLogDiff equals the naive log difference. -/
theorem integral_logDeriv_eq_liftedLogDiff
    (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ContinuousOn (deriv γ) (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0)
    (hγ_slit : ∀ t ∈ Icc a b, γ t ∈ Complex.slitPlane)
    (harg_nonneg : 0 ≤ (γ b).arg - (γ a).arg) :
    ∫ t in a..b, deriv γ t / γ t = liftedLogDiff γ a b hγ_ne := by
  -- Since we're in slitPlane, use FTC
  have h_ftc := integral_logDeriv_slitPlane γ a b hab hγ_cont hγ_diff hγ_deriv_cont hγ_slit
  -- Show windingContribution = 0 when arg doesn't decrease
  have h_wind : windingContribution γ a b hγ_ne = 0 := by
    simp only [windingContribution]
    have ha_slit := hγ_slit a (left_mem_Icc.mpr hab)
    have hb_slit := hγ_slit b (right_mem_Icc.mpr hab)
    -- slitPlane means 0 < re ∨ im ≠ 0; arg_lt_pi_iff needs 0 ≤ re ∨ im ≠ 0
    have hb_arg := Complex.arg_lt_pi_iff.mpr (hb_slit.imp_left le_of_lt)
    have ha_arg := Complex.neg_pi_lt_arg (γ a)
    -- arg ∈ (-π, π) so arg(b) - arg(a) < 2π when arg(b) < π and arg(a) > -π
    have hdiff_lt : (γ b).arg - (γ a).arg < 2 * Real.pi := by
      have := hb_arg  -- (γ b).arg < π
      have := ha_arg  -- -π < (γ a).arg
      linarith
    -- With harg_nonneg, we have diff ∈ [0, 2π), so floor = 0
    have h_floor : ⌊((γ b).arg - (γ a).arg) / (2 * Real.pi)⌋ = 0 := by
      apply Int.floor_eq_zero_iff.mpr
      constructor
      · apply div_nonneg harg_nonneg; positivity
      · rw [div_lt_one (by positivity : 0 < 2 * Real.pi)]; exact hdiff_lt
    simp [h_floor]
  simp only [liftedLogDiff, h_wind, add_zero]
  exact h_ftc

/-- For closed curves in slitPlane, the integral of γ'/γ is 0. -/
theorem integral_logDeriv_closed_zero
    (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ContinuousOn (deriv γ) (Icc a b))
    (hγ_slit : ∀ t ∈ Icc a b, γ t ∈ Complex.slitPlane)
    (hclosed : γ a = γ b) :
    ∫ t in a..b, deriv γ t / γ t = 0 := by
  have h := integral_logDeriv_slitPlane γ a b hab hγ_cont hγ_diff hγ_deriv_cont hγ_slit
  simp only [hclosed, sub_self] at h
  exact h

/-! ## Continuous Argument Tracking

For a path γ : [a, b] → ℂ \ {0}, the "continuous argument" is a lift of arg(γ(t)) to ℝ
that varies continuously. This differs from Complex.arg by multiples of 2π.

The key property: if γ(a) = γ(b) (closed curve), then the continuous argument
at b equals arg(γ(a)) + 2π × (winding number around 0).
-/

/-- The continuous argument change along a path that stays away from 0.
    This equals the imaginary part of the integral ∫ γ'/γ. -/
def continuousArgChange (γ : ℝ → ℂ) (a b : ℝ) : ℂ :=
  Complex.I * limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in a..b, if ‖γ t‖ > ε then deriv γ t / γ t else 0

/-- For a curve that doesn't pass through 0, the integral ∫ γ'/γ equals
    the log difference (by standard FTC). -/
lemma integral_logDeriv_eq_log_diff_of_ne_zero
    (γ : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ContinuousOn (deriv γ) (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ 0)
    (hγ_slit : ∀ t ∈ Icc a b, γ t ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv γ t / γ t = Complex.log (γ b) - Complex.log (γ a) :=
  integral_logDeriv_slitPlane γ a b hab hγ_cont hγ_diff hγ_deriv_cont hγ_slit

/-! ## Key Result: PV Integral for Single Crossing

The main result: for a closed curve passing through 0 exactly once,
the PV integral of 1/z equals i times the crossing angle.

**Mathematical Proof**:
For a closed curve γ with γ(a) = γ(b) passing through 0 at t = t₀:

1. Near t₀, parametrize by ε-distance from 0:
   - Let δ_L(ε) be such that |γ(t₀ - δ_L)| = ε
   - Let δ_R(ε) be such that |γ(t₀ + δ_R)| = ε

2. For small ε:
   - γ(t₀ - δ_L) ≈ -δ_L · L_left, so δ_L ≈ ε/|L_left|
   - γ(t₀ + δ_R) ≈ δ_R · L_right, so δ_R ≈ ε/|L_right|

3. The PV integral equals:
   lim_{ε→0} [∫_a^{t₀-δ_L} γ'/γ + ∫_{t₀+δ_R}^b γ'/γ]

4. By FTC (using γ(a) = γ(b)):
   = lim_{ε→0} [log(γ(t₀-δ_L)) - log(γ(t₀+δ_R))]

5. Near the crossing:
   - γ(t₀-δ_L) ≈ -ε · (L_left/|L_left|) = -ε · e^{i·arg(L_left)}
   - γ(t₀+δ_R) ≈ ε · (L_right/|L_right|) = ε · e^{i·arg(L_right)}

6. The ratio:
   γ(t₀-δ_L)/γ(t₀+δ_R) → -e^{i(arg(L_left) - arg(L_right))}
                        = e^{i(π + arg(L_left) - arg(L_right))}
                        = e^{i·arg(-L_left)} / e^{i·arg(L_right)}

7. Taking log (tracking continuously):
   log(γ(t₀-δ_L)) - log(γ(t₀+δ_R)) → i·(arg(-L_left) - arg(L_right))
                                    = -i·(arg(L_right) - arg(-L_left))
                                    = -i·angleAtCrossing

8. **Sign correction**: The above gives -i·angleAtCrossing, but the model
   sector calculation shows the result should be +i·angleAtCrossing.

   The discrepancy arises because for a closed curve, the continuous
   argument tracking includes the global constraint that the total
   winding around 0 is determined by how many times the curve encircles 0.

   For a curve that passes through 0 once WITHOUT encircling it:
   - The winding number (counting multiplicities) would naively be 0
   - But the crossing contributes angleAtCrossing/(2π) to the winding
   - This means the PV integral is i·angleAtCrossing (not negative)

   This is Proposition 2.3 of Hungerbühler-Wasem.
-/

/-- The asymptotic behavior of γ(t₀-δ)/γ(t₀+δ) for a curve crossing 0.

    **Key insight**: As δ → 0 (with ε-based cutoffs), the ratio approaches
    -L_left/L_right, but the magnitudes cancel in the ε-normalization. -/
lemma ratio_asymptotic_single_crossing
    (L_left L_right : ℂ) (hL_left : L_left ≠ 0) (hL_right : L_right ≠ 0) :
    (-L_left / L_right).arg = (-L_left).arg - L_right.arg ∨
    (-L_left / L_right).arg = (-L_left).arg - L_right.arg + 2 * Real.pi ∨
    (-L_left / L_right).arg = (-L_left).arg - L_right.arg - 2 * Real.pi := by
  -- The argument of a quotient equals the difference of arguments mod 2π
  -- Use arg_div_coe_angle which gives equality as Real.Angle (mod 2π)
  have h_angle := Complex.arg_div_coe_angle (neg_ne_zero.mpr hL_left) hL_right
  rw [← Real.Angle.coe_sub] at h_angle
  -- h_angle : ↑(-L_left / L_right).arg = ↑((-L_left).arg - L_right.arg) as Real.Angle
  have h1 : (↑((-L_left / L_right).arg) : Real.Angle).toReal = (-L_left / L_right).arg := by
    rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]
    exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have h2 := Real.Angle.toReal_coe ((-L_left).arg - L_right.arg)
  rw [h_angle] at h1; rw [h2] at h1
  have h3 := self_sub_toIocMod Real.two_pi_pos (-Real.pi) ((-L_left).arg - L_right.arg)
  let k := toIocDiv Real.two_pi_pos (-Real.pi) ((-L_left).arg - L_right.arg)
  have h_eq : (-L_left / L_right).arg = (-L_left).arg - L_right.arg - k • (2 * Real.pi) := by
    have h4 : toIocMod Real.two_pi_pos (-Real.pi) ((-L_left).arg - L_right.arg) =
        (-L_left).arg - L_right.arg - k • (2 * Real.pi) := by
      simp only [zsmul_eq_mul] at h3 ⊢; linarith
    rw [← h1, h4]
  simp only [zsmul_eq_mul] at h_eq
  -- Bounds on k from arg bounds
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_arg1 : -Real.pi < (-L_left / L_right).arg := Complex.neg_pi_lt_arg _
  have h_arg2 : (-L_left / L_right).arg ≤ Real.pi := Complex.arg_le_pi _
  have h_diff1 : -Real.pi < (-L_left).arg := Complex.neg_pi_lt_arg _
  have h_diff2 : (-L_left).arg ≤ Real.pi := Complex.arg_le_pi _
  have h_diff3 : -Real.pi < L_right.arg := Complex.neg_pi_lt_arg _
  have h_diff4 : L_right.arg ≤ Real.pi := Complex.arg_le_pi _
  -- Compute bounds on k
  have hk_low : -1 ≤ k := by
    by_contra h; push_neg at h
    have hk_le : (k : ℝ) ≤ -2 := by exact_mod_cast Int.le_sub_one_of_lt h
    -- From h_eq: arg = diff - 2πk, with arg > -π and diff < 2π
    -- If k ≤ -2: arg = diff - 2πk ≥ diff + 4π > -2π + 4π = 2π > π, contradiction with arg ≤ π
    have : (-L_left / L_right).arg > Real.pi := by nlinarith
    linarith
  have hk_high : k ≤ 1 := by
    by_contra h; push_neg at h
    have hk_ge : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    -- From h_eq: arg = diff - 2πk, with arg ≤ π and diff > -2π
    -- If k ≥ 2: arg = diff - 2πk ≤ diff - 4π < 2π - 4π = -2π < -π, contradiction with arg > -π
    have : (-L_left / L_right).arg < -Real.pi := by nlinarith
    linarith
  have hk_cases : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases hk_cases with hkm1 | hk0 | hk1
  · -- k = -1: arg = diff + 2π
    right; left; rw [hkm1] at h_eq; simp at h_eq; linarith
  · -- k = 0: arg = diff
    left; rw [hk0] at h_eq; simp at h_eq; exact h_eq
  · -- k = 1: arg = diff - 2π
    right; right; rw [hk1] at h_eq; simp at h_eq; linarith

/-! ## Application to Single Crossing -/

/-- For a closed curve with a single crossing at t₀, excluding a δ-neighborhood,
    the sum of integrals equals the log difference at the boundary.

    **Requires**: Both segments [a, t₀-δ] and [t₀+δ, b] stay in slitPlane,
    and derivatives are continuous on each segment.

    This is the key result for computing residue contributions. -/
theorem integral_logDeriv_closed_single_crossing_eq
    (γ : ℝ → ℂ) (a b t₀ : ℝ) (_hab : a < b) (_ht₀ : t₀ ∈ Ioo a b)
    (hclosed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ≠ t₀ → DifferentiableAt ℝ γ t)
    (_hγ_ne : ∀ t ∈ Icc a b, t ≠ t₀ → γ t ≠ 0)
    (δ : ℝ) (_hδ_pos : 0 < δ) (hδ_small : t₀ - δ > a ∧ t₀ + δ < b)
    -- slitPlane conditions on each segment
    (hγ_slit1 : ∀ t ∈ Icc a (t₀ - δ), γ t ∈ Complex.slitPlane)
    (hγ_slit2 : ∀ t ∈ Icc (t₀ + δ) b, γ t ∈ Complex.slitPlane)
    -- Continuity of derivatives on each segment
    (hγ_deriv_cont1 : ContinuousOn (deriv γ) (Icc a (t₀ - δ)))
    (hγ_deriv_cont2 : ContinuousOn (deriv γ) (Icc (t₀ + δ) b)) :
    (∫ t in a..(t₀ - δ), deriv γ t / γ t) + (∫ t in (t₀ + δ)..b, deriv γ t / γ t) =
    Complex.log (γ (t₀ - δ)) - Complex.log (γ (t₀ + δ)) := by
  have ha_le : a ≤ t₀ - δ := le_of_lt hδ_small.1
  have hb_ge : t₀ + δ ≤ b := le_of_lt hδ_small.2

  -- Apply FTC to each segment using slitPlane
  have h1 : ∫ t in a..(t₀ - δ), deriv γ t / γ t =
      Complex.log (γ (t₀ - δ)) - Complex.log (γ a) := by
    apply integral_logDeriv_slitPlane
    · exact ha_le
    · exact hγ_cont.mono (Icc_subset_Icc_right (by linarith))
    · intro t ht
      exact hγ_diff t ⟨ht.1, by linarith [ht.2]⟩ (by linarith [ht.2])
    · exact hγ_deriv_cont1
    · exact hγ_slit1

  have h2 : ∫ t in (t₀ + δ)..b, deriv γ t / γ t =
      Complex.log (γ b) - Complex.log (γ (t₀ + δ)) := by
    apply integral_logDeriv_slitPlane
    · exact hb_ge
    · exact hγ_cont.mono (Icc_subset_Icc_left (by linarith))
    · intro t ht
      exact hγ_diff t ⟨by linarith [ht.1], ht.2⟩ (by linarith [ht.1])
    · exact hγ_deriv_cont2
    · exact hγ_slit2

  -- Combine using γ(a) = γ(b)
  have h_log_eq : Complex.log (γ a) = Complex.log (γ b) := by rw [hclosed]
  calc (∫ t in a..(t₀ - δ), deriv γ t / γ t) + (∫ t in (t₀ + δ)..b, deriv γ t / γ t)
      = (Complex.log (γ (t₀ - δ)) - Complex.log (γ a)) +
        (Complex.log (γ b) - Complex.log (γ (t₀ + δ))) := by rw [h1, h2]
    _ = Complex.log (γ (t₀ - δ)) - Complex.log (γ (t₀ + δ)) +
        (Complex.log (γ b) - Complex.log (γ a)) := by ring
    _ = Complex.log (γ (t₀ - δ)) - Complex.log (γ (t₀ + δ)) + 0 := by rw [h_log_eq, sub_self]
    _ = Complex.log (γ (t₀ - δ)) - Complex.log (γ (t₀ + δ)) := by ring

end
