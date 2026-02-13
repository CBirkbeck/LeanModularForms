/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary

/-!
# Parameterized FD Boundary

Height-parameterized versions of the FD boundary curve and q-radius,
for the existential-height approach (Ticket E2).

## Main Definitions

* `fdBoundary_H H` — FD boundary at height `H`
* `seg5_q_radius_H H` — q-radius at height `H`

## Main Results

* `fdBoundary_H_eq_fdBoundary` — bridge at canonical height
* `fdBoundary_H_closed` — curve is closed for any H
* `seg5_q_radius_H_anti` — q-radius is antitone in H
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Parameterized Segment Definitions -/

/-- Segment 1 (right vertical) at height H. -/
def fdBoundary_seg1_H (H : ℝ) : ℝ → ℂ := fun t =>
  1/2 + (H - t * (H - Real.sqrt 3 / 2)) * I

/-- Segment 2 (arc ρ' → i) — does not depend on H. -/
def fdBoundary_seg2_H : ℝ → ℂ := fdBoundary_seg2

/-- Segment 3 (arc i → ρ) — does not depend on H. -/
def fdBoundary_seg3_H : ℝ → ℂ := fdBoundary_seg3

/-- Segment 4 (left vertical) at height H. -/
def fdBoundary_seg4_H (H : ℝ) : ℝ → ℂ := fun t =>
  -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2)) * I

/-- Segment 5 (top horizontal) at height H. -/
def fdBoundary_seg5_H (H : ℝ) : ℝ → ℂ := fun t =>
  (t - 9/2) + H * I

/-! ## Full Parameterized Boundary -/

/-- The FD boundary curve parameterized by height `H`, over [0, 5]. -/
def fdBoundary_H (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    1/2 + (H - t * (H - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  else if t ≤ 3 then
    Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  else if t ≤ 4 then
    -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2)) * I
  else
    (t - 9/2) + H * I

/-! ## Bridge at Canonical Height -/

/-- `fdBoundary_H H_height` is definitionally `fdBoundary`. -/
theorem fdBoundary_H_eq_fdBoundary : fdBoundary_H H_height = fdBoundary := rfl

/-! ## Endpoint Lemmas (H-dependent: t = 0, 4, 5) -/

theorem fdBoundary_H_at_zero (H : ℝ) :
    fdBoundary_H H 0 = (1/2 : ℂ) + ↑H * I := by
  simp only [fdBoundary_H]
  simp only [show (0 : ℝ) ≤ 1 from by norm_num, ↓reduceIte]
  congr 1; congr 1
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]

theorem fdBoundary_H_at_four (H : ℝ) :
    fdBoundary_H H 4 = -(1/2 : ℂ) + ↑H * I := by
  simp only [fdBoundary_H]
  have h1 : ¬((4 : ℝ) ≤ 1) := by norm_num
  have h2 : ¬((4 : ℝ) ≤ 2) := by norm_num
  have h3 : ¬((4 : ℝ) ≤ 3) := by norm_num
  have h4 : (4 : ℝ) ≤ 4 := le_refl 4
  simp only [h1, ↓reduceIte, h2, h3, h4]
  push_cast; ring

theorem fdBoundary_H_at_five (H : ℝ) :
    fdBoundary_H H 5 = (1/2 : ℂ) + ↑H * I := by
  simp only [fdBoundary_H]
  have h1 : ¬((5 : ℝ) ≤ 1) := by norm_num
  have h2 : ¬((5 : ℝ) ≤ 2) := by norm_num
  have h3 : ¬((5 : ℝ) ≤ 3) := by norm_num
  have h4 : ¬((5 : ℝ) ≤ 4) := by norm_num
  simp only [h1, ↓reduceIte, h2, h3, h4]
  congr 1
  push_cast; norm_num

/-! ## Endpoint Lemmas (H-independent: t = 1, 2, 3) -/

theorem fdBoundary_H_at_one (H : ℝ) :
    fdBoundary_H H 1 = fdBoundary 1 := by
  simp only [fdBoundary_H, fdBoundary]
  simp only [show (1 : ℝ) ≤ 1 from le_refl 1, ↓reduceIte]
  congr 1; congr 1
  push_cast; ring

theorem fdBoundary_H_at_two (H : ℝ) :
    fdBoundary_H H 2 = fdBoundary 2 := by
  simp only [fdBoundary_H, fdBoundary]
  simp only [show ¬((2 : ℝ) ≤ 1) from by norm_num,
             show (2 : ℝ) ≤ 2 from le_refl 2, ↓reduceIte]

theorem fdBoundary_H_at_three (H : ℝ) :
    fdBoundary_H H 3 = fdBoundary 3 := by
  simp only [fdBoundary_H, fdBoundary]
  simp only [show ¬((3 : ℝ) ≤ 1) from by norm_num,
             show ¬((3 : ℝ) ≤ 2) from by norm_num,
             show (3 : ℝ) ≤ 3 from le_refl 3, ↓reduceIte]

/-! ## Closure -/

/-- The parameterized boundary is closed for any height H. -/
theorem fdBoundary_H_closed (H : ℝ) :
    fdBoundary_H H 0 = fdBoundary_H H 5 := by
  rw [fdBoundary_H_at_zero, fdBoundary_H_at_five]

/-! ## Parameterized q-Radius -/

/-- The q-radius at height H: `exp(-2πH)`. -/
def seg5_q_radius_H (H : ℝ) : ℝ := Real.exp (-2 * Real.pi * H)

theorem seg5_q_radius_H_pos (H : ℝ) : 0 < seg5_q_radius_H H :=
  Real.exp_pos _

theorem seg5_q_radius_H_ne_zero (H : ℝ) : seg5_q_radius_H H ≠ 0 :=
  ne_of_gt (seg5_q_radius_H_pos H)

/-! ## q-Radius Monotonicity -/

/-- q-radius is antitone: larger H gives smaller radius. -/
theorem seg5_q_radius_H_anti {H₁ H₂ : ℝ} (h : H₁ ≤ H₂) :
    seg5_q_radius_H H₂ ≤ seg5_q_radius_H H₁ := by
  unfold seg5_q_radius_H
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])

/-- Closed ball inclusion from q-radius monotonicity. -/
theorem closedBall_seg5_q_radius_H_anti {H₁ H₂ : ℝ} (h : H₁ ≤ H₂) :
    Metric.closedBall (0 : ℂ) (seg5_q_radius_H H₂) ⊆
    Metric.closedBall (0 : ℂ) (seg5_q_radius_H H₁) :=
  Metric.closedBall_subset_closedBall (seg5_q_radius_H_anti h)

/-- Cusp nonvanishing transfers to smaller heights (larger balls). -/
theorem cusp_nonvanishing_seg5_q_radius_H_mono {k : ℤ} (f : ModularForm (Gamma 1) k)
    {H₁ H₂ : ℝ} (h : H₁ ≤ H₂)
    (hnonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H₁),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H₂),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0 :=
  fun q hq hq_ne => hnonvan q (closedBall_seg5_q_radius_H_anti h hq) hq_ne

/-! ## Segment Continuity -/

theorem continuous_fdBoundary_seg1_H (H : ℝ) : Continuous (fdBoundary_seg1_H H) := by
  unfold fdBoundary_seg1_H; fun_prop

theorem continuous_fdBoundary_seg4_H (H : ℝ) : Continuous (fdBoundary_seg4_H H) := by
  unfold fdBoundary_seg4_H; fun_prop

theorem continuous_fdBoundary_seg5_H (H : ℝ) : Continuous (fdBoundary_seg5_H H) := by
  unfold fdBoundary_seg5_H; fun_prop

/-! ## HasDerivAt for Linear Segments -/

theorem hasDerivAt_fdBoundary_seg1_H (H : ℝ) (t : ℝ) :
    HasDerivAt (fdBoundary_seg1_H H) (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have hfun : fdBoundary_seg1_H H = fun s : ℝ =>
      ((1 : ℂ) / 2 + ↑H * I) + ↑s * (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) := by
    ext s; simp only [fdBoundary_seg1_H]; push_cast; ring
  rw [hfun]
  exact (((hasDerivAt_id t).ofReal_comp).mul_const _).const_add _
    |>.congr_deriv (by push_cast; ring)

theorem hasDerivAt_fdBoundary_seg4_H (H : ℝ) (t : ℝ) :
    HasDerivAt (fdBoundary_seg4_H H) ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have hfun : fdBoundary_seg4_H H = fun s : ℝ =>
      (-(1 : ℂ) / 2 + (↑(Real.sqrt 3 / 2) - 3 * ↑(H - Real.sqrt 3 / 2)) * I) +
      ↑s * ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) := by
    ext s; simp only [fdBoundary_seg4_H]; push_cast; ring
  rw [hfun]
  exact (((hasDerivAt_id t).ofReal_comp).mul_const _).const_add _
    |>.congr_deriv (by push_cast; ring)

theorem hasDerivAt_fdBoundary_seg5_H (H : ℝ) (t : ℝ) :
    HasDerivAt (fdBoundary_seg5_H H) 1 t := by
  have hfun : fdBoundary_seg5_H H = fun s : ℝ =>
      (-(9 : ℂ) / 2 + ↑H * I) + ↑s * 1 := by
    ext s; simp only [fdBoundary_seg5_H]; ring
  rw [hfun]
  exact (((hasDerivAt_id t).ofReal_comp).mul_const _).const_add _
    |>.congr_deriv (by push_cast; ring)

/-! ## Deriv Formulas -/

theorem deriv_fdBoundary_seg1_H (H : ℝ) (t : ℝ) :
    deriv (fdBoundary_seg1_H H) t = -(↑(H - Real.sqrt 3 / 2) : ℂ) * I :=
  (hasDerivAt_fdBoundary_seg1_H H t).deriv

theorem deriv_fdBoundary_seg4_H (H : ℝ) (t : ℝ) :
    deriv (fdBoundary_seg4_H H) t = (↑(H - Real.sqrt 3 / 2) : ℂ) * I :=
  (hasDerivAt_fdBoundary_seg4_H H t).deriv

theorem deriv_fdBoundary_seg5_H (H : ℝ) (t : ℝ) :
    deriv (fdBoundary_seg5_H H) t = 1 :=
  (hasDerivAt_fdBoundary_seg5_H H t).deriv

/-! ## Nonvanishing Derivatives -/

theorem deriv_fdBoundary_seg1_H_ne_zero {H : ℝ} (hH : Real.sqrt 3 / 2 < H) (t : ℝ) :
    deriv (fdBoundary_seg1_H H) t ≠ 0 := by
  rw [deriv_fdBoundary_seg1_H]
  exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (sub_pos.mpr hH).ne'))
    Complex.I_ne_zero

theorem deriv_fdBoundary_seg4_H_ne_zero {H : ℝ} (hH : Real.sqrt 3 / 2 < H) (t : ℝ) :
    deriv (fdBoundary_seg4_H H) t ≠ 0 := by
  rw [deriv_fdBoundary_seg4_H]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (sub_pos.mpr hH).ne') Complex.I_ne_zero

theorem deriv_fdBoundary_seg5_H_ne_zero (H : ℝ) (t : ℝ) :
    deriv (fdBoundary_seg5_H H) t ≠ 0 := by
  rw [deriv_fdBoundary_seg5_H]; exact one_ne_zero

/-! ## Derivative Norm Formulas -/

theorem norm_deriv_fdBoundary_seg1_H {H : ℝ} (hH : Real.sqrt 3 / 2 < H) (t : ℝ) :
    ‖deriv (fdBoundary_seg1_H H) t‖ = H - Real.sqrt 3 / 2 := by
  rw [deriv_fdBoundary_seg1_H, neg_mul, norm_neg, norm_mul,
      Complex.norm_of_nonneg (le_of_lt (sub_pos.mpr hH)), Complex.norm_I, mul_one]

theorem norm_deriv_fdBoundary_seg4_H {H : ℝ} (hH : Real.sqrt 3 / 2 < H) (t : ℝ) :
    ‖deriv (fdBoundary_seg4_H H) t‖ = H - Real.sqrt 3 / 2 := by
  rw [deriv_fdBoundary_seg4_H, norm_mul,
      Complex.norm_of_nonneg (le_of_lt (sub_pos.mpr hH)), Complex.norm_I, mul_one]

theorem norm_deriv_fdBoundary_seg5_H (H : ℝ) (t : ℝ) :
    ‖deriv (fdBoundary_seg5_H H) t‖ = 1 := by
  rw [deriv_fdBoundary_seg5_H, norm_one]

/-! ## Uniform Derivative Bound -/

/-- All linear segment derivatives have norm ≤ max(H - √3/2, 1). -/
theorem norm_deriv_linear_segments_le {H : ℝ} (hH : Real.sqrt 3 / 2 < H) (t : ℝ) :
    ‖deriv (fdBoundary_seg1_H H) t‖ ≤ max (H - Real.sqrt 3 / 2) 1 ∧
    ‖deriv (fdBoundary_seg4_H H) t‖ ≤ max (H - Real.sqrt 3 / 2) 1 ∧
    ‖deriv (fdBoundary_seg5_H H) t‖ ≤ max (H - Real.sqrt 3 / 2) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_deriv_fdBoundary_seg1_H hH]; exact le_max_left _ _
  · rw [norm_deriv_fdBoundary_seg4_H hH]; exact le_max_left _ _
  · rw [norm_deriv_fdBoundary_seg5_H]; exact le_max_right _ _

/-! ## Full Curve Continuity -/

/-- The full parameterized boundary `fdBoundary_H H` is continuous. -/
theorem fdBoundary_H_continuous (H : ℝ) : Continuous (fdBoundary_H H) := by
  unfold fdBoundary_H
  apply Continuous.if
  -- Junction at t = 1: seg1_H(1) = exp(πi/3) (H cancels)
  · intro t ht
    rw [show {t : ℝ | t ≤ 1} = Set.Iic 1 from rfl, frontier_Iic] at ht
    simp only [mem_singleton_iff] at ht
    subst ht
    simp only [show (1:ℝ) ≤ 2 from by norm_num, ↓reduceIte]
    have h_angle : (↑Real.pi / 3 + (↑(1:ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ) =
        ↑Real.pi / 3 := by push_cast; ring
    rw [h_angle, Complex.exp_mul_I]
    have h_cos : Complex.cos (↑Real.pi / 3 : ℂ) = 1/2 := by
      have heq : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by
        simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
      rw [heq, ← Complex.ofReal_cos, Real.cos_pi_div_three]; norm_num
    have h_sin : Complex.sin (↑Real.pi / 3 : ℂ) = ↑(Real.sqrt 3) / 2 := by
      have heq : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by
        simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
      rw [heq, ← Complex.ofReal_sin, Real.sin_pi_div_three]; push_cast; ring
    rw [h_cos, h_sin]
    simp only [Complex.ofReal_one, one_mul, sub_sub_cancel]
  -- Continuity of segment 1
  · exact Continuous.add continuous_const (Continuous.mul (Continuous.sub continuous_const
      (Continuous.mul continuous_ofReal continuous_const)) continuous_const)
  -- Else: remaining segments
  · apply Continuous.if
    -- Junction at t = 2: both sides equal exp(πi/2)
    · intro t ht
      rw [show {t : ℝ | t ≤ 2} = Set.Iic 2 from rfl, frontier_Iic] at ht
      simp only [mem_singleton_iff] at ht
      subst ht
      simp only [show (2:ℝ) ≤ 3 from by norm_num, ↓reduceIte]
      congr 1
      have lhs_simp : (↑Real.pi / 3 + (↑(2:ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ)
                    = ↑Real.pi / 2 := by push_cast; field_simp; ring
      have rhs_simp : (↑Real.pi / 2 + (↑(2:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ)
                    = ↑Real.pi / 2 := by push_cast; field_simp; ring
      rw [lhs_simp, rhs_simp]
    -- Continuity of segment 2
    · apply Continuous.cexp
      apply Continuous.mul _ continuous_const
      apply Continuous.add continuous_const
      exact Continuous.mul (continuous_ofReal.sub continuous_const) continuous_const
    -- Else: remaining segments
    · apply Continuous.if
      -- Junction at t = 3: exp(2πi/3) = -1/2 + √3/2·I (H cancels)
      · intro t ht
        rw [show {t : ℝ | t ≤ 3} = Set.Iic 3 from rfl, frontier_Iic] at ht
        simp only [mem_singleton_iff] at ht
        subst ht
        have lhs_simp : (↑Real.pi / 2 + (↑(3:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ)
                      = 2 * ↑Real.pi / 3 := by push_cast; field_simp; ring
        have rhs_simp : (↑(Real.sqrt 3) / 2 + (↑(3:ℝ) - 3) * (↑H - ↑(Real.sqrt 3) / 2) : ℂ)
                      = ↑(Real.sqrt 3) / 2 := by push_cast; ring
        conv_lhs => rw [lhs_simp]
        conv_rhs => rw [rhs_simp]
        rw [Complex.exp_mul_I]
        have h_cos : Complex.cos (2 * ↑Real.pi / 3 : ℂ) = -1/2 := by
          have h1 : (2 * ↑Real.pi / 3 : ℂ) = ↑Real.pi - ↑Real.pi / 3 := by ring
          rw [h1, Complex.cos_sub, Complex.cos_pi, Complex.sin_pi]
          have h2 : Complex.cos (↑Real.pi / 3 : ℂ) = (1 / 2 : ℂ) := by
            have heq : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by
              simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
            rw [heq, ← Complex.ofReal_cos, Real.cos_pi_div_three]; norm_num
          rw [h2]; ring
        have h_sin : Complex.sin (2 * ↑Real.pi / 3 : ℂ) = ↑(Real.sqrt 3) / 2 := by
          have h1 : (2 * ↑Real.pi / 3 : ℂ) = ↑Real.pi - ↑Real.pi / 3 := by ring
          rw [h1, Complex.sin_sub, Complex.sin_pi, Complex.cos_pi]
          have h2 : Complex.sin (↑Real.pi / 3 : ℂ) = ↑(Real.sqrt 3) / 2 := by
            have heq : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by
              simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
            rw [heq, ← Complex.ofReal_sin, Real.sin_pi_div_three]; push_cast; ring
          rw [h2]; ring
        rw [h_cos, h_sin]
        simp only [show (3:ℝ) ≤ 4 from by norm_num, ↓reduceIte]
      -- Continuity of segment 3
      · apply Continuous.cexp
        apply Continuous.mul _ continuous_const
        apply Continuous.add continuous_const
        exact Continuous.mul (continuous_ofReal.sub continuous_const) continuous_const
      -- Else: final two segments
      · apply Continuous.if
        -- Junction at t = 4: seg4_H(4) = seg5_H(4) = -1/2 + H·I
        · intro t ht
          rw [show {t : ℝ | t ≤ 4} = Set.Iic 4 from rfl, frontier_Iic] at ht
          simp only [mem_singleton_iff] at ht
          subst ht
          have lhs_simp : (↑(Real.sqrt 3) / 2 + (↑(4:ℝ) - 3) *
              (↑H - ↑(Real.sqrt 3) / 2) : ℂ) = ↑H := by push_cast; ring
          have rhs_simp : ((↑(4:ℝ) : ℂ) - 9/2 : ℂ) = -1/2 := by push_cast; ring
          conv_lhs => rw [lhs_simp]
          conv_rhs => rw [rhs_simp]
        -- Continuity of segment 4
        · apply Continuous.add continuous_const
          apply Continuous.mul _ continuous_const
          apply Continuous.add continuous_const
          exact Continuous.mul (continuous_ofReal.sub continuous_const) continuous_const
        -- Continuity of segment 5
        · apply Continuous.add _ continuous_const
          exact continuous_ofReal.sub continuous_const

/-! ## Segment Agreement with Full Curve -/

theorem fdBoundary_H_eq_seg1_H {H : ℝ} {t : ℝ} (ht : t ≤ 1) :
    fdBoundary_H H t = fdBoundary_seg1_H H t := by
  simp only [fdBoundary_H, fdBoundary_seg1_H, ht, ↓reduceIte]

theorem fdBoundary_H_eq_seg2_H {H : ℝ} {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : t ≤ 2) :
    fdBoundary_H H t = fdBoundary_seg2_H t := by
  simp only [fdBoundary_H, fdBoundary_seg2_H, fdBoundary_seg2, ht1, ↓reduceIte, ht2]

theorem fdBoundary_H_eq_seg3_H {H : ℝ} {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2))
    (ht3 : t ≤ 3) :
    fdBoundary_H H t = fdBoundary_seg3_H t := by
  simp only [fdBoundary_H, fdBoundary_seg3_H, fdBoundary_seg3, ht1, ↓reduceIte, ht2, ht3]

theorem fdBoundary_H_eq_seg4_H {H : ℝ} {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2))
    (ht3 : ¬(t ≤ 3)) (ht4 : t ≤ 4) :
    fdBoundary_H H t = fdBoundary_seg4_H H t := by
  simp only [fdBoundary_H, fdBoundary_seg4_H, ht1, ↓reduceIte, ht2, ht3, ht4]

theorem fdBoundary_H_eq_seg5_H {H : ℝ} {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2))
    (ht3 : ¬(t ≤ 3)) (ht4 : ¬(t ≤ 4)) :
    fdBoundary_H H t = fdBoundary_seg5_H H t := by
  simp only [fdBoundary_H, fdBoundary_seg5_H, ht1, ↓reduceIte, ht2, ht3, ht4]

/-! ## Compatibility at Canonical Height -/

/-- At canonical height, `fdBoundary_H` equals `fdBoundary` pointwise. -/
theorem fdBoundary_H_height_eq (t : ℝ) : fdBoundary_H H_height t = fdBoundary t := by
  rfl

/-! ## Arc Unification

Segments 2 and 3 are the same smooth function `exp(π(1+t)/6 · I)` on `(1, 3)`.
This means the join at `t = 2` is smooth (no corner). -/

/-- The arc segments agree with a single smooth function on `(1, 3)`. -/
theorem fdBoundary_H_eq_arc {H : ℝ} {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    fdBoundary_H H t = Complex.exp (↑(Real.pi * (1 + t) / 6) * I) := by
  simp only [fdBoundary_H, show ¬(t ≤ 1) from by linarith, ↓reduceIte]
  by_cases h2 : t ≤ 2
  · simp only [h2, ↓reduceIte]; congr 1; push_cast; ring
  · simp only [h2, ↓reduceIte, show t ≤ 3 from le_of_lt ht3]; congr 1; push_cast; ring

/-! ## Differentiability Partition -/

/-- The corner points of `fdBoundary_H` (where it is NOT differentiable). -/
def fdBoundary_H_partition : Finset ℝ := {1, 3, 4}

/-- HasDerivAt for the unified arc function `exp(π(1+s)/6 · I)`. -/
private theorem hasDerivAt_arc (t : ℝ) :
    HasDerivAt (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I))
      (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
  have hfun : (fun s : ℝ => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) =
      (fun s : ℝ => Complex.exp (↑(Real.pi / 6) * I + ↑(Real.pi / 6) * I * ↑s)) := by
    ext s; congr 1; push_cast; ring
  rw [hfun]
  have hinner : HasDerivAt (fun s : ℝ => ↑(Real.pi / 6) * I + ↑(Real.pi / 6) * I * (↑s : ℂ))
      (↑(Real.pi / 6) * I) t :=
    ((hasDerivAt_id (𝕜 := ℝ) t).ofReal_comp.const_mul (↑(Real.pi / 6) * I)).const_add _
      |>.congr_deriv (by simp only [Complex.ofReal_one, mul_one])
  exact hinner.cexp.congr_deriv (by rw [mul_comm]; congr 1; congr 1; push_cast; ring)

/-! ## Differentiability Off Partition -/

/-- `fdBoundary_H H` is differentiable at every point not in `{1, 3, 4}`. -/
theorem fdBoundary_H_differentiableAt_off_partition (H : ℝ) {t : ℝ}
    (ht : t ∉ fdBoundary_H_partition) :
    DifferentiableAt ℝ (fdBoundary_H H) t := by
  simp only [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton] at ht
  push_neg at ht
  obtain ⟨h1, h3, h4⟩ := ht
  by_cases ht1 : t < 1
  · -- t < 1: locally equals seg1 (affine)
    have heq : fdBoundary_H H =ᶠ[𝓝 t] fdBoundary_seg1_H H :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Iio 1, Iio_mem_nhds ht1,
        fun s hs => fdBoundary_H_eq_seg1_H (le_of_lt hs)⟩
    exact heq.differentiableAt_iff.mpr (hasDerivAt_fdBoundary_seg1_H H t).differentiableAt
  · push_neg at ht1
    by_cases ht3' : t < 3
    · -- 1 < t < 3: locally equals the unified arc function
      have ht1' : 1 < t := lt_of_le_of_ne ht1 (Ne.symm h1)
      have heq : fdBoundary_H H =ᶠ[𝓝 t]
          (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3, Ioo_mem_nhds ht1' ht3',
          fun s hs => fdBoundary_H_eq_arc hs.1 hs.2⟩
      exact heq.differentiableAt_iff.mpr (hasDerivAt_arc t).differentiableAt
    · push_neg at ht3'
      by_cases ht4' : t < 4
      · -- 3 < t < 4: locally equals seg4 (affine)
        have ht3'' : 3 < t := lt_of_le_of_ne ht3' (Ne.symm h3)
        have heq : fdBoundary_H H =ᶠ[𝓝 t] fdBoundary_seg4_H H :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 3 4, Ioo_mem_nhds ht3'' ht4',
            fun s hs => fdBoundary_H_eq_seg4_H (by linarith [hs.1])
              (by linarith [hs.1]) (by linarith [hs.1]) (le_of_lt hs.2)⟩
        exact heq.differentiableAt_iff.mpr (hasDerivAt_fdBoundary_seg4_H H t).differentiableAt
      · -- 4 < t: locally equals seg5 (affine)
        push_neg at ht4'
        have ht4'' : 4 < t := lt_of_le_of_ne ht4' (Ne.symm h4)
        have heq : fdBoundary_H H =ᶠ[𝓝 t] fdBoundary_seg5_H H :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioi 4, Ioi_mem_nhds ht4'',
            fun s hs => by
              have hs' : 4 < s := hs
              exact fdBoundary_H_eq_seg5_H (by linarith) (by linarith)
                (by linarith) (by linarith)⟩
        exact heq.differentiableAt_iff.mpr (hasDerivAt_fdBoundary_seg5_H H t).differentiableAt

/-! ## Smooth Join at t = 2 -/

/-- `fdBoundary_H H` has an explicit derivative at t = 2 (arc junction, NOT a corner). -/
theorem fdBoundary_H_hasDerivAt_t2 (H : ℝ) :
    HasDerivAt (fdBoundary_H H)
      (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * 3 / 6) * I)) 2 := by
  have heq : fdBoundary_H H =ᶠ[𝓝 2]
      (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3, Ioo_mem_nhds (by norm_num) (by norm_num),
      fun s hs => fdBoundary_H_eq_arc hs.1 hs.2⟩
  have harc := hasDerivAt_arc 2
  have hval : Real.pi * (1 + 2) / 6 = Real.pi * 3 / 6 := by ring
  rw [hval] at harc
  exact heq.hasDerivAt_iff.mpr harc

/-! ## Full-Curve HasDerivAt on Each Piece -/

/-- On `(-∞, 1)`, `fdBoundary_H H` has the seg1 derivative. -/
theorem fdBoundary_H_hasDerivAt_seg1 (H : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fdBoundary_H H) (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have heq : fdBoundary_H H =ᶠ[𝓝 t] fdBoundary_seg1_H H :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Iio 1, Iio_mem_nhds ht,
      fun s hs => fdBoundary_H_eq_seg1_H (le_of_lt hs)⟩
  exact heq.hasDerivAt_iff.mpr (hasDerivAt_fdBoundary_seg1_H H t)

/-- On `(1, 3)`, `fdBoundary_H H` has the arc derivative. -/
theorem fdBoundary_H_hasDerivAt_arc (H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    HasDerivAt (fdBoundary_H H)
      (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
  have heq : fdBoundary_H H =ᶠ[𝓝 t]
      (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3, Ioo_mem_nhds ht1 ht3,
      fun s hs => fdBoundary_H_eq_arc hs.1 hs.2⟩
  exact heq.hasDerivAt_iff.mpr (hasDerivAt_arc t)

/-- On `(3, 4)`, `fdBoundary_H H` has the seg4 derivative. -/
theorem fdBoundary_H_hasDerivAt_seg4 (H : ℝ) {t : ℝ} (ht3 : 3 < t) (ht4 : t < 4) :
    HasDerivAt (fdBoundary_H H) ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
  have heq : fdBoundary_H H =ᶠ[𝓝 t] fdBoundary_seg4_H H :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 3 4, Ioo_mem_nhds ht3 ht4,
      fun s hs => fdBoundary_H_eq_seg4_H (by linarith [hs.1])
        (by linarith [hs.1]) (by linarith [hs.1]) (le_of_lt hs.2)⟩
  exact heq.hasDerivAt_iff.mpr (hasDerivAt_fdBoundary_seg4_H H t)

/-- On `(4, ∞)`, `fdBoundary_H H` has the seg5 derivative. -/
theorem fdBoundary_H_hasDerivAt_seg5 (H : ℝ) {t : ℝ} (ht4 : 4 < t) :
    HasDerivAt (fdBoundary_H H) 1 t := by
  have heq : fdBoundary_H H =ᶠ[𝓝 t] fdBoundary_seg5_H H :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioi 4, Ioi_mem_nhds ht4,
      fun s (hs : 4 < s) => fdBoundary_H_eq_seg5_H (by linarith)
        (by linarith) (by linarith) (by linarith)⟩
  exact heq.hasDerivAt_iff.mpr (hasDerivAt_fdBoundary_seg5_H H t)

/-! ## Derivative Norm Bound for Full Curve -/

/-- The derivative of `fdBoundary_H H` is bounded on `[0, 5]` off the partition. -/
theorem fdBoundary_H_deriv_bound_ex {H : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, t ∉ fdBoundary_H_partition →
      ‖deriv (fdBoundary_H H) t‖ ≤ M := by
  refine ⟨max (H - Real.sqrt 3 / 2) 1, lt_max_of_lt_right one_pos, ?_⟩
  intro t ht
  simp only [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton] at ht
  push_neg at ht
  obtain ⟨h1, h3, h4⟩ := ht
  by_cases ht1 : t < 1
  · rw [(fdBoundary_H_hasDerivAt_seg1 H ht1).deriv, neg_mul, norm_neg, norm_mul,
        Complex.norm_of_nonneg (le_of_lt (sub_pos.mpr hH)), Complex.norm_I, mul_one]
    exact le_max_left _ _
  · push_neg at ht1
    by_cases ht3 : t < 3
    · have ht1' : 1 < t := lt_of_le_of_ne ht1 (Ne.symm h1)
      rw [(fdBoundary_H_hasDerivAt_arc H ht1' ht3).deriv, norm_mul, norm_mul,
          Complex.norm_of_nonneg (le_of_lt (by positivity : (0 : ℝ) < Real.pi / 6)),
          Complex.norm_I, mul_one]
      have : ‖Complex.exp (↑(Real.pi * (1 + t) / 6) * I)‖ = 1 := by
        rw [Complex.norm_exp_ofReal_mul_I]
      rw [this, mul_one]
      have hpi6 : Real.pi / 6 ≤ 1 := by
        have := Real.pi_le_four; linarith
      exact le_trans hpi6 (le_max_right _ _)
    · push_neg at ht3
      by_cases ht4 : t < 4
      · have ht3' : 3 < t := lt_of_le_of_ne ht3 (Ne.symm h3)
        rw [(fdBoundary_H_hasDerivAt_seg4 H ht3' ht4).deriv, norm_mul,
            Complex.norm_of_nonneg (le_of_lt (sub_pos.mpr hH)), Complex.norm_I, mul_one]
        exact le_max_left _ _
      · push_neg at ht4
        have ht4' : 4 < t := lt_of_le_of_ne ht4 (Ne.symm h4)
        rw [(fdBoundary_H_hasDerivAt_seg5 H ht4').deriv, norm_one]
        exact le_max_right _ _

/-! ## Piecewise Continuity of Derivative -/

/-- The derivative is continuous on `(0, 1)` (seg1: constant). -/
theorem fdBoundary_H_deriv_continuousOn_Ioo_01 (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Set.Ioo 0 1) := by
  intro t ht
  have : deriv (fdBoundary_H H) =ᶠ[𝓝 t]
      fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I := by
    have hmem : Set.Ioo 0 1 ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 0 1, hmem,
      fun s hs => (fdBoundary_H_hasDerivAt_seg1 H hs.2).deriv⟩
  exact this.continuousAt.continuousWithinAt

/-- The derivative is continuous on `(1, 3)` (arc: smooth). -/
theorem fdBoundary_H_deriv_continuousOn_Ioo_13 (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Set.Ioo 1 3) := by
  intro t ht
  have hderiv_eq : deriv (fdBoundary_H H) =ᶠ[𝓝 t]
      fun s => ↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + s) / 6) * I) := by
    have hmem : Set.Ioo 1 3 ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 1 3, hmem,
      fun s hs => (fdBoundary_H_hasDerivAt_arc H hs.1 hs.2).deriv⟩
  have hcont : Continuous
      (fun s : ℝ => ↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) := by
    apply Continuous.mul continuous_const
    apply Continuous.cexp
    apply Continuous.mul _ continuous_const
    have : (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ)) =
        Complex.ofReal ∘ (fun s : ℝ => Real.pi * (1 + s) / 6) := by ext; simp
    rw [this]
    exact continuous_ofReal.comp (by fun_prop)
  exact (hcont.continuousAt.congr hderiv_eq.symm).continuousWithinAt

/-- The derivative is continuous on `(3, 4)` (seg4: constant). -/
theorem fdBoundary_H_deriv_continuousOn_Ioo_34 (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Set.Ioo 3 4) := by
  intro t ht
  have : deriv (fdBoundary_H H) =ᶠ[𝓝 t]
      fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I := by
    have hmem : Set.Ioo 3 4 ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 3 4, hmem,
      fun s hs => (fdBoundary_H_hasDerivAt_seg4 H hs.1 hs.2).deriv⟩
  exact this.continuousAt.continuousWithinAt

/-- The derivative is continuous on `(4, 5)` (seg5: constant). -/
theorem fdBoundary_H_deriv_continuousOn_Ioo_45 (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Set.Ioo 4 5) := by
  intro t ht
  have : deriv (fdBoundary_H H) =ᶠ[𝓝 t]
      fun _ => (1 : ℂ) := by
    have hmem : Set.Ioo 4 5 ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 4 5, hmem,
      fun s hs => (fdBoundary_H_hasDerivAt_seg5 H (by linarith [hs.1])).deriv⟩
  exact this.continuousAt.continuousWithinAt

/-! ## Non-Differentiability at Corner Points

Strategy: assume `DifferentiableAt`, get `HasDerivAt`, restrict to left/right `HasDerivWithinAt`,
use `EventuallyEq.hasDerivWithinAt_iff` to transfer from segment functions, then
`UniqueDiffWithinAt.eq_deriv` forces left derivative = right derivative, contradiction. -/

/-- Helper: `fdBoundary_seg4_H H` agrees with `fdBoundary_H H` near 4 from the left. -/
private theorem seg4_eventuallyEq_left (H : ℝ) :
    fdBoundary_seg4_H H =ᶠ[nhdsWithin 4 (Set.Iic 4)] fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  exact ⟨Set.Ioo 3 5 ∩ Set.Iic 4, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin,
    fun s hs => (fdBoundary_H_eq_seg4_H (by linarith [hs.1.1])
      (by linarith [hs.1.1]) (by linarith [hs.1.1]) hs.2).symm⟩

/-- Helper: `fdBoundary_seg5_H H` agrees with `fdBoundary_H H` near 4 from the right. -/
private theorem seg5_eventuallyEq_right (H : ℝ) :
    fdBoundary_seg5_H H =ᶠ[nhdsWithin 4 (Set.Ici 4)] fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Set.Ioo 3 5 ∩ Set.Ici 4, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs => ?_⟩
  have hs_ici : (4 : ℝ) ≤ s := hs.2
  rcases eq_or_lt_of_le hs_ici with rfl | h
  · -- s = 4: both equal -1/2 + H*I
    simp only [fdBoundary_seg5_H, fdBoundary_H_at_four]; push_cast; ring
  · -- 4 < s: use fdBoundary_H_eq_seg5_H
    exact (fdBoundary_H_eq_seg5_H (by linarith [h])
      (by linarith [h]) (by linarith [h]) (by linarith [h])).symm

/-- `fdBoundary_H H` is NOT differentiable at `t = 4` (seg4 → seg5 junction). -/
theorem fdBoundary_H_not_differentiableAt_4 {H : ℝ} (hH : Real.sqrt 3 / 2 < H) :
    ¬DifferentiableAt ℝ (fdBoundary_H H) 4 := by
  intro hdiff
  have hval4 : fdBoundary_seg4_H H 4 = fdBoundary_H H 4 := by
    simp only [fdBoundary_seg4_H, fdBoundary_H_at_four]; push_cast; ring
  have hval5 : fdBoundary_seg5_H H 4 = fdBoundary_H H 4 := by
    simp only [fdBoundary_seg5_H, fdBoundary_H_at_four]; push_cast; ring
  have hleft : HasDerivWithinAt (fdBoundary_H H)
      ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Set.Iic 4) 4 :=
    ((seg4_eventuallyEq_left H).hasDerivWithinAt_iff hval4).mp
      (hasDerivAt_fdBoundary_seg4_H H 4).hasDerivWithinAt
  have hright : HasDerivWithinAt (fdBoundary_H H) 1 (Set.Ici 4) 4 :=
    ((seg5_eventuallyEq_right H).hasDerivWithinAt_iff hval5).mp
      (hasDerivAt_fdBoundary_seg5_H H 4).hasDerivWithinAt
  have hd := hdiff.hasDerivAt
  have eq1 := (uniqueDiffWithinAt_Iic (4 : ℝ)).eq_deriv _ hleft hd.hasDerivWithinAt
  have eq2 := (uniqueDiffWithinAt_Ici (4 : ℝ)).eq_deriv _ hright hd.hasDerivWithinAt
  -- eq1: (↑(H - Real.sqrt 3 / 2) : ℂ) * I = deriv (fdBoundary_H H) 4
  -- eq2: 1 = deriv (fdBoundary_H H) 4
  -- So: (↑(H - Real.sqrt 3 / 2) : ℂ) * I = 1
  have heq : (↑(H - Real.sqrt 3 / 2) : ℂ) * I = 1 := eq1.trans eq2.symm
  have him := congr_arg Complex.im heq
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, Complex.one_im] at him
  linarith [sub_pos.mpr hH]

/-- Helper: arc function agrees with `fdBoundary_H H` near 3 from the left. -/
private theorem arc_eventuallyEq_left_3 (H : ℝ) :
    (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) =ᶠ[nhdsWithin 3 (Set.Iic 3)]
    fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Set.Ioo 2 4 ∩ Set.Iic 3, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs => ?_⟩
  have hs1 : 1 < s := by linarith [hs.1.1]
  have hs3 : s ≤ 3 := hs.2
  rcases eq_or_lt_of_le hs3 with rfl | hs3'
  · -- s = 3: need arc(3) = fdBoundary_H H 3
    conv_rhs => rw [show fdBoundary_H H 3 = fdBoundary 3 from fdBoundary_H_at_three H]
    simp only [fdBoundary, show ¬(3:ℝ) ≤ 1 from by norm_num, ↓reduceIte,
      show ¬(3:ℝ) ≤ 2 from by norm_num, show (3:ℝ) ≤ 3 from le_rfl]
    congr 1; push_cast; ring
  · exact (fdBoundary_H_eq_arc hs1 hs3').symm

/-- Helper: seg4 agrees with `fdBoundary_H H` near 3 from the right. -/
private theorem seg4_eventuallyEq_right_3 (H : ℝ) :
    fdBoundary_seg4_H H =ᶠ[nhdsWithin 3 (Set.Ici 3)] fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Set.Ioo 2 4 ∩ Set.Ici 3, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs => ?_⟩
  have hs_ge : (3 : ℝ) ≤ s := hs.2
  rcases eq_or_lt_of_le hs_ge with rfl | h
  · -- s = 3: both equal ρ = -1/2 + √3/2*I
    rw [show fdBoundary_H H 3 = fdBoundary 3 from fdBoundary_H_at_three H, fdBoundary_at_three]
    simp only [fdBoundary_seg4_H, ellipticPoint_rho, ellipticPoint_rho']
    simp only [UpperHalfPlane.coe_mk_subtype]
    push_cast; ring
  · -- 3 < s: use fdBoundary_H_eq_seg4_H
    exact (fdBoundary_H_eq_seg4_H (by linarith [hs.1.1]) (by linarith [hs.1.1])
      (by linarith [h]) (by linarith [hs.1.2])).symm

/-- `fdBoundary_H H` is NOT differentiable at `t = 3` (arc → seg4 junction). -/
theorem fdBoundary_H_not_differentiableAt_3 {H : ℝ} (_hH : Real.sqrt 3 / 2 < H) :
    ¬DifferentiableAt ℝ (fdBoundary_H H) 3 := by
  intro hdiff
  -- Value equality: arc(3) = fdBoundary_H H 3
  have hval_arc : (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) 3 =
      fdBoundary_H H 3 := by
    rw [show fdBoundary_H H 3 = fdBoundary 3 from fdBoundary_H_at_three H]
    simp only [fdBoundary, show ¬(3:ℝ) ≤ 1 from by norm_num, ↓reduceIte,
      show ¬(3:ℝ) ≤ 2 from by norm_num, show (3:ℝ) ≤ 3 from le_rfl]
    congr 1; push_cast; ring
  -- Value equality: seg4(3) = fdBoundary_H H 3
  have hval_seg4 : fdBoundary_seg4_H H 3 = fdBoundary_H H 3 := by
    rw [show fdBoundary_H H 3 = fdBoundary 3 from fdBoundary_H_at_three H, fdBoundary_at_three]
    simp only [fdBoundary_seg4_H, ellipticPoint_rho, ellipticPoint_rho']
    simp only [UpperHalfPlane.coe_mk_subtype]
    push_cast; ring
  -- Left derivative (from arc): (π/6)*I*exp(2πi/3)
  have hleft : HasDerivWithinAt (fdBoundary_H H)
      (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * 4 / 6) * I)) (Set.Iic 3) 3 :=
    ((arc_eventuallyEq_left_3 H).hasDerivWithinAt_iff hval_arc).mp
      ((hasDerivAt_arc 3).hasDerivWithinAt.congr_deriv (by congr 1; congr 1; ring))
  -- Right derivative (from seg4): (H-√3/2)*I
  have hright : HasDerivWithinAt (fdBoundary_H H)
      ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Set.Ici 3) 3 :=
    ((seg4_eventuallyEq_right_3 H).hasDerivWithinAt_iff hval_seg4).mp
      (hasDerivAt_fdBoundary_seg4_H H 3).hasDerivWithinAt
  -- Uniqueness forces left = right derivative
  have hd := hdiff.hasDerivAt
  have eq1 := (uniqueDiffWithinAt_Iic (3 : ℝ)).eq_deriv _ hleft hd.hasDerivWithinAt
  have eq2 := (uniqueDiffWithinAt_Ici (3 : ℝ)).eq_deriv _ hright hd.hasDerivWithinAt
  have heq : ↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * 4 / 6) * I) =
      (↑(H - Real.sqrt 3 / 2) : ℂ) * I := eq1.trans eq2.symm
  -- Compare real parts: LHS.re = -(π/6)*sin(2π/3) ≠ 0, RHS.re = 0
  have hre := congr_arg Complex.re heq
  have hre_rhs : ((↑(H - Real.sqrt 3 / 2) : ℂ) * I).re = 0 := by
    simp [Complex.mul_re]
  have hre_lhs : (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * 4 / 6) * I)).re =
      -(Real.pi / 6) * Real.sin (Real.pi * 4 / 6) := by
    rw [mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.I_mul_re, Complex.exp_ofReal_mul_I_im]
    ring
  rw [hre_lhs, hre_rhs] at hre
  have hsin : Real.sin (Real.pi * 4 / 6) = Real.sqrt 3 / 2 := by
    rw [show Real.pi * 4 / 6 = Real.pi - Real.pi / 3 from by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [hsin] at hre
  nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]

/-- Helper: seg1 agrees with `fdBoundary_H H` near 1 from the left. -/
private theorem seg1_eventuallyEq_left_1 (H : ℝ) :
    fdBoundary_seg1_H H =ᶠ[nhdsWithin 1 (Set.Iic 1)] fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  exact ⟨Set.Ioo 0 2 ∩ Set.Iic 1, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin,
    fun s hs => (fdBoundary_H_eq_seg1_H hs.2).symm⟩

/-- Helper: arc function agrees with `fdBoundary_H H` near 1 from the right. -/
private theorem arc_eventuallyEq_right_1 (H : ℝ) :
    (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) =ᶠ[nhdsWithin 1 (Set.Ici 1)]
    fdBoundary_H H := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨Set.Ioo 0 2 ∩ Set.Ici 1, Filter.inter_mem
    (nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num)))
    self_mem_nhdsWithin, fun s hs => ?_⟩
  have hs_ge : (1 : ℝ) ≤ s := hs.2
  rcases eq_or_lt_of_le hs_ge with rfl | hs1
  · -- s = 1: evaluate exp(π/3*I) = 1/2 + √3/2*I = fdBoundary_H H 1
    show Complex.exp (↑(Real.pi * (1 + 1) / 6) * I) = fdBoundary_H H 1
    simp only [fdBoundary_H, show (1:ℝ) ≤ 1 from le_rfl, ↓reduceIte]
    rw [show (↑(Real.pi * (1 + 1) / 6 : ℝ) : ℂ) * I = ↑(Real.pi / 3 : ℝ) * I
      from by push_cast; ring, Complex.exp_mul_I]
    rw [show (↑(Real.pi / 3 : ℝ) : ℂ) = ↑(Real.pi / 3) from rfl,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  · exact (fdBoundary_H_eq_arc hs1 (by linarith [hs.1.2])).symm

/-- `fdBoundary_H H` is NOT differentiable at `t = 1` (seg1 → arc junction). -/
theorem fdBoundary_H_not_differentiableAt_1 {H : ℝ} (_hH : Real.sqrt 3 / 2 < H) :
    ¬DifferentiableAt ℝ (fdBoundary_H H) 1 := by
  intro hdiff
  -- Value equality: seg1(1) = fdBoundary_H H 1
  have hval_seg1 : fdBoundary_seg1_H H 1 = fdBoundary_H H 1 :=
    (fdBoundary_H_eq_seg1_H le_rfl).symm
  -- Value equality: arc(1) = fdBoundary_H H 1 (via trig: exp(π/3*I) = 1/2 + √3/2*I)
  have hval_arc : (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) 1 =
      fdBoundary_H H 1 := by
    show Complex.exp (↑(Real.pi * (1 + 1) / 6) * I) = fdBoundary_H H 1
    simp only [fdBoundary_H, show (1:ℝ) ≤ 1 from le_rfl, ↓reduceIte]
    rw [show (↑(Real.pi * (1 + 1) / 6 : ℝ) : ℂ) * I = ↑(Real.pi / 3 : ℝ) * I
      from by push_cast; ring, Complex.exp_mul_I]
    rw [show (↑(Real.pi / 3 : ℝ) : ℂ) = ↑(Real.pi / 3) from rfl,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  -- Left derivative (from seg1): -(H-√3/2)*I
  have hleft : HasDerivWithinAt (fdBoundary_H H)
      (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Set.Iic 1) 1 :=
    ((seg1_eventuallyEq_left_1 H).hasDerivWithinAt_iff hval_seg1).mp
      (hasDerivAt_fdBoundary_seg1_H H 1).hasDerivWithinAt
  -- Right derivative (from arc): (π/6)*I*exp(π/3*I)
  have hright : HasDerivWithinAt (fdBoundary_H H)
      (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * 2 / 6) * I)) (Set.Ici 1) 1 :=
    ((arc_eventuallyEq_right_1 H).hasDerivWithinAt_iff hval_arc).mp
      ((hasDerivAt_arc 1).hasDerivWithinAt.congr_deriv (by congr 1; congr 1; ring))
  -- Uniqueness forces left = right derivative
  have hd := hdiff.hasDerivAt
  have eq1 := (uniqueDiffWithinAt_Iic (1 : ℝ)).eq_deriv _ hleft hd.hasDerivWithinAt
  have eq2 := (uniqueDiffWithinAt_Ici (1 : ℝ)).eq_deriv _ hright hd.hasDerivWithinAt
  have heq : -(↑(H - Real.sqrt 3 / 2) : ℂ) * I =
      ↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * 2 / 6) * I) := eq1.trans eq2.symm
  -- Compare real parts: LHS.re = 0, RHS.re = -(π/6)*sin(π/3) ≠ 0
  have hre := congr_arg Complex.re heq
  have hre_lhs : (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I).re = 0 := by
    simp [Complex.mul_re]
  have hre_rhs : (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * 2 / 6) * I)).re =
      -(Real.pi / 6) * Real.sin (Real.pi * 2 / 6) := by
    rw [mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.I_mul_re, Complex.exp_ofReal_mul_I_im]
    ring
  rw [hre_lhs, hre_rhs] at hre
  rw [show Real.pi * 2 / 6 = Real.pi / 3 from by ring] at hre
  rw [Real.sin_pi_div_three] at hre
  -- hre : 0 = -(π/6) * (√3/2), contradiction since π > 0 and √3 > 0
  nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]

end
