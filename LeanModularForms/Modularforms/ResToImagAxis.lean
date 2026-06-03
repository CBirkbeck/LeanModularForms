/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.QExpansion

public import LeanModularForms.Modularforms.AtImInfty
public import LeanModularForms.Modularforms.SlashActionAuxil

@[expose] public section

/-!
# Restriction of functions on the upper half-plane to the imaginary axis

For a function `F : ℍ → ℂ` we define its restriction `ResToImagAxis F : ℝ → ℂ` to the
positive imaginary axis by `t ↦ F (I * t)` for `t > 0` and `0` otherwise. We then study
the algebraic structure (realness, positivity, eventual positivity) of this restriction
under addition, multiplication and scaling, and establish polynomial-decay results that
apply in particular to cusp forms.

## Main definitions

* `ResToImagAxis F`: the restriction `t ↦ F (I * t)`.
* `ResToImagAxis.Real F`: `F` is real-valued on the positive imaginary axis.
* `ResToImagAxis.Pos F`: `F` is real-valued and positive on the positive imaginary axis.
* `ResToImagAxis.EventuallyPos F`: `F` is real-valued and positive for large enough `t > 0`.

## Main results

* `ResToImagAxis.Differentiable`: `F.resToImagAxis` is real-differentiable at `t > 0`
  whenever `F` is `MDiff`.
* `ResToImagAxis.SlashActionS`: behaviour of the restriction under the slash action of `S`.
* `cuspForm_rpow_mul_resToImagAxis_tendsto_zero`: any cusp form of level `Γ(n)` satisfies
  `t ^ s * f (it) → 0` as `t → ∞`.
* `isBigO_atImInfty_of_fourier_shift`: a Fourier expansion starting at index `n₀ > 0`
  gives an `O(exp(-2π n₀ · im z))` bound at `atImInfty`.
-/

open UpperHalfPlane hiding I

open Real Complex ContinuousMap Matrix CongruenceSubgroup ModularGroup Filter Asymptotics

open scoped Interval Real Topology Manifold ModularForm MatrixGroups

/--
Restrict a function `F : ℍ → ℂ` to the positive imaginary axis, i.e. `t ↦ F (I * t)`.
If $t \le 0$, then `F (I * t)` is not defined, and we return `0` in that case.
-/
noncomputable def ResToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t ↦ if ht : 0 < t then F ⟨(I * t), by simp [ht]⟩ else 0

namespace Function

/-- Dot notation alias for `ResToImagAxis`. -/
noncomputable def resToImagAxis (F : ℍ → ℂ) : ℝ → ℂ := ResToImagAxis F

@[simp] lemma resToImagAxis_eq_resToImagAxis (F : ℍ → ℂ) :
    F.resToImagAxis = ResToImagAxis F := rfl

@[simp] lemma resToImagAxis_apply (F : ℍ → ℂ) (t : ℝ) :
    F.resToImagAxis t = ResToImagAxis F t := rfl

end Function

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is real-valued,
i.e. imaginary part is zero.
-/
@[fun_prop]
noncomputable def ResToImagAxis.Real (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → (F.resToImagAxis t).im = 0

/--
Function $F : \mathbb{H} \to \mathbb{C}$ is real and positive on the imaginary axis.
-/
@[fun_prop]
noncomputable def ResToImagAxis.Pos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∀ t : ℝ, 0 < t → 0 < (F.resToImagAxis t).re

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is eventually
positive, i.e. there exists $t_0 > 0$ such that for all $t \ge t_0$, $F(it)$ is real and positive.
-/
@[fun_prop]
noncomputable def ResToImagAxis.EventuallyPos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, t₀ ≤ t → 0 < (F.resToImagAxis t).re

/-- The restriction `F.resToImagAxis` is real-differentiable at every `t > 0` whenever `F`
is manifold-differentiable on `ℍ`. -/
@[fun_prop]
theorem ResToImagAxis.Differentiable (F : ℍ → ℂ) (hF : MDiff F) (t : ℝ)
    (ht : 0 < t) : DifferentiableAt ℝ F.resToImagAxis t := by
  rw [Function.resToImagAxis_eq_resToImagAxis]
  have hmdiff := hF ⟨Complex.I * t, by norm_num [Complex.I_re, ht]⟩
  rw [mdifferentiableAt_iff] at hmdiff
  have h_diff : DifferentiableAt ℝ (fun t : ℝ ↦ F (ofComplex (Complex.I * t))) t := by
    convert hmdiff.restrictScalars ℝ |> DifferentiableAt.comp t <|
      DifferentiableAt.const_mul ofRealCLM.differentiableAt _ using 1
  refine h_diff.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with t ht
  simp_all only [ResToImagAxis, ↓reduceDIte]
  rw [ofComplex_apply_of_im_pos]

/-- Restriction and slash action under `S`: `(F ∣[k] S) (it) = (it) ^ (-k) * F (it)`. -/
theorem ResToImagAxis.SlashActionS (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    (F ∣[k] S).resToImagAxis t = Complex.I ^ (-k) * t ^ (-k) * F.resToImagAxis (1 / t) := by
  set z : ℍ := ⟨I * t, by simp [ht]⟩ with hzdef
  set z' : ℍ := ⟨I * (1 / t : ℝ), by simpa [one_div_pos.2 ht]⟩ with hz'def
  have h : mk (-z)⁻¹ z.im_inv_neg_coe_pos = z' :=
    UpperHalfPlane.ext (by simp [hzdef, hz'def, mul_comm])
  have hslash : (F ∣[k] S) z = I ^ (-k) * t ^ (-k) * F z' := by
    rw [modular_slash_S_apply, h]
    simp [hzdef, mul_zpow I (t : ℂ) (-k), mul_comm (F z')]
  simpa [ResToImagAxis, ht, hz'def] using hslash

/-- The constant function `t ↦ c` with `c : ℝ` is real-valued on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.const (c : ℝ) : ResToImagAxis.Real (fun _ ↦ c) := by
  intro t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, ofReal_im]

/-- The zero function is real-valued on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.zero : ResToImagAxis.Real (fun _ ↦ 0) := ResToImagAxis.Real.const 0

/-- The constant function `1` is real-valued on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.one : ResToImagAxis.Real (fun _ ↦ 1) := ResToImagAxis.Real.const 1

/-- Negation preserves realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.neg {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (-F) := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, hFreal]

/-- Addition preserves realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F + G) := by
  intro t ht
  have hFreal := hF t ht
  have hGreal := hG t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp [ResToImagAxis, ht, hFreal, hGreal]

/-- Subtraction preserves realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.sub {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F - G) := by
  simpa [sub_eq_add_neg] using ResToImagAxis.Real.add hF hG.neg

/-- Multiplication preserves realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F * G) := by
  intro t ht
  have hFreal := hF t ht
  have hGreal := hG t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp [ResToImagAxis, ht, hFreal, hGreal]

/-- Real scalar multiplication preserves realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (c • F) := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, hFreal]

/-- Natural powers preserve realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) (n : ℕ) :
    ResToImagAxis.Real (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.Real.one
  | succ n hn => exact hn.mul hF

/-- A positive real constant function is positive on the imaginary axis. -/
theorem ResToImagAxis.Pos.const (c : ℝ) (hc : 0 < c) : ResToImagAxis.Pos (fun _ ↦ c) :=
  ⟨ResToImagAxis.Real.const c, fun t ht ↦ by simp [ResToImagAxis, ht, hc]⟩

/-- The constant function `1` is positive on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Pos.one : ResToImagAxis.Pos (fun _ ↦ 1) :=
  ResToImagAxis.Pos.const 1 one_pos

/-- Addition preserves positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Pos.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F + G) := by
  refine ⟨Real.add hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos hGpos
  simp [ResToImagAxis, ht, add_pos hFpos hGpos]

/-- Multiplication preserves positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Pos.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F * G) := by
  refine ⟨Real.mul hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFreal := hF.1 t ht
  have hGreal := hG.1 t ht
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal hFpos hGpos
  simp [ResToImagAxis, ht, hFreal, hGreal, mul_pos hFpos hGpos]

/-- Positive scalar multiplication preserves positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Pos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Pos F)
    (hc : 0 < c) : ResToImagAxis.Pos (c • F) := by
  refine ⟨Real.smul hF.1, fun t ht ↦ ?_⟩
  have hFpos := hF.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos
  simp [ResToImagAxis, ht, mul_pos hc hFpos]

/-- Natural powers preserve positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Pos.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) (n : ℕ) :
    ResToImagAxis.Pos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.Pos.one
  | succ n hn => exact hn.mul hF

/-- Positivity on the imaginary axis implies eventual positivity (with threshold `1`). -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.from_pos {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) :
    ResToImagAxis.EventuallyPos F :=
  ⟨hF.1, 1, by positivity, fun t ht ↦ hF.2 t (by linarith)⟩

/-- The constant function `1` is eventually positive on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.one :
    ResToImagAxis.EventuallyPos (fun _ ↦ 1) :=
  ResToImagAxis.EventuallyPos.from_pos ResToImagAxis.Pos.one

/-- A positive real constant function is eventually positive on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.const (c : ℝ) (hc : 0 < c) :
    ResToImagAxis.EventuallyPos (fun _ ↦ c) :=
  ResToImagAxis.EventuallyPos.from_pos (ResToImagAxis.Pos.const c hc)

/-- Addition preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.add {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F + G) := by
  refine ⟨ResToImagAxis.Real.add hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  refine ⟨max tF tG, by positivity, fun t ht ↦ ?_⟩
  have htpos : 0 < t := hF0.trans_le ((le_max_left tF tG).trans ht)
  have hFpos_t := hFpos t ((le_max_left tF tG).trans ht)
  have hGpos_t := hGpos t ((le_max_right tF tG).trans ht)
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos]
  exact add_pos hFpos_t hGpos_t

/-- Multiplication preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.mul {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F * G) := by
  refine ⟨ResToImagAxis.Real.mul hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  refine ⟨max tF tG, by positivity, fun t ht ↦ ?_⟩
  have htpos : 0 < t := hF0.trans_le ((le_max_left tF tG).trans ht)
  have hFreal_t := hF.1 t htpos
  have hGreal_t := hG.1 t htpos
  have hFpos_t := hFpos t ((le_max_left tF tG).trans ht)
  have hGpos_t := hGpos t ((le_max_right tF tG).trans ht)
  simp only [Function.resToImagAxis, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFreal_t hGreal_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos, ↓reduceDIte, Pi.mul_apply, mul_re,
    hFreal_t, hGreal_t, mul_zero, sub_zero]
  exact mul_pos hFpos_t hGpos_t

/-- Natural powers preserve eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.pow {F : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (n : ℕ) :
    ResToImagAxis.EventuallyPos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.EventuallyPos.one
  | succ n hn => exact hn.mul hF

/-- Positive scalar multiplication preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.EventuallyPos F)
    (hc : 0 < c) : ResToImagAxis.EventuallyPos (c • F) := by
  refine ⟨ResToImagAxis.Real.smul hF.1, ?_⟩
  obtain ⟨t₀, hF0, hFpos⟩ := hF.2
  refine ⟨t₀, hF0, fun t ht ↦ ?_⟩
  have htpos : 0 < t := hF0.trans_le ht
  have hFpos_t := hFpos t ht
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFpos_t
  simp [ResToImagAxis, htpos, mul_pos hc hFpos_t]


/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
the restriction to the imaginary axis `t ↦ F(it)` is `O(exp(-c * t))` at `atTop`.
-/
lemma isBigO_resToImagAxis_of_isBigO_atImInfty {F : ℍ → ℂ} {c : ℝ} (_hc : 0 < c)
    (hF : F =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) :
    F.resToImagAxis =O[atTop] fun t ↦ Real.exp (-c * t) := by
  rw [Asymptotics.isBigO_iff] at hF ⊢
  obtain ⟨C, hC⟩ := hF
  obtain ⟨A, hA⟩ := Filter.eventually_atImInfty.mp hC
  refine ⟨C, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max A 1)] with t ht
  have ht_pos : 0 < t := one_pos.trans_le (le_of_max_le_right ht)
  simp only [Function.resToImagAxis, ResToImagAxis, ht_pos, ↓reduceDIte]
  set z : ℍ := ⟨Complex.I * t, by simp [ht_pos]⟩
  have him : z.im = t := by change (Complex.I * t).im = t; simp
  simpa [him] using hA z (by simpa [him] using le_of_max_le_left ht)

/--
The analytic kernel: if `g : ℝ → ℂ` is eventually bounded by `C * exp(-b * t)` for some
`b > 0`, then `t^s * g(t) → 0` as `t → ∞` for any real power `s`.

This follows from the fact that `t^s * exp(-b * t) → 0` (mathlib's
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`) combined with the big-O transfer lemma.
-/
lemma tendsto_rpow_mul_of_isBigO_exp {g : ℝ → ℂ} {s b : ℝ} (hb : 0 < b)
    (hg : g =O[atTop] fun t ↦ rexp (-b * t)) :
    Tendsto (fun t : ℝ ↦ (t : ℂ) ^ (s : ℂ) * g t) atTop (𝓝 0) := by
  refine ((isBigO_refl _ _).mul (Complex.isBigO_ofReal_right.mpr hg)).trans_tendsto ?_
  refine (tendsto_ofReal_iff.mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.le]

/--
If `F : ℍ → ℂ` is `O(exp(-c * im τ))` at `atImInfty` for some `c > 0`, then
`t^s * F(it) → 0` as `t → ∞` for any real power `s`.
-/
theorem tendsto_rpow_mul_resToImagAxis_of_isBigO_exp {F : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : F =O[atImInfty] fun τ ↦ rexp (-c * τ.im)) (s : ℝ) :
    Tendsto (fun t : ℝ ↦ (t : ℂ) ^ (s : ℂ) * F.resToImagAxis t) atTop (𝓝 0) :=
  tendsto_rpow_mul_of_isBigO_exp hc (isBigO_resToImagAxis_of_isBigO_atImInfty hc hF)

/--
For a cusp form `f` of level `Γ(n)`, we have `t^s * f(it) → 0` as `t → ∞` for any real power `s`.

This follows from the exponential decay of cusp forms at infinity: `f = O(exp(-2π τ.im / n))`.
-/
theorem cuspForm_rpow_mul_resToImagAxis_tendsto_zero {n : ℕ} {k : ℤ} {F : Type*}
    [NeZero n] [FunLike F ℍ ℂ] [CuspFormClass F Γ(n) k] (f : F) (s : ℝ) :
    Tendsto (fun t : ℝ ↦ (t : ℂ) ^ (s : ℂ) * (f : ℍ → ℂ).resToImagAxis t) atTop (𝓝 0) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hmem : (n : ℝ) ∈ (Γ(n) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simpa only [strictPeriods_Gamma] using AddSubgroup.mem_zmultiples (n : ℝ)
  have hdecay' : (f : ℍ → ℂ) =O[atImInfty] fun τ ↦ rexp (-(2 * π / n) * τ.im) := by
    convert CuspFormClass.exp_decay_atImInfty hn_pos hmem (f := f) using 2 with τ
    field_simp
  exact tendsto_rpow_mul_resToImagAxis_of_isBigO_exp (div_pos (by positivity) hn_pos) hdecay' s

/-- Real part of the Fourier exponent `2πi(m+n₀)w` is `-2π(m+n₀)·im w`. -/
private lemma mul_re_two_pi_I_natCast (m n₀ : ℕ) (w : ℂ) :
    (2 * π * I * ((m + n₀ : ℕ) : ℂ) * w).re = -(2 * π) * (m + n₀) * w.im := by
  simp [Complex.mul_re, Complex.mul_im]

/--
For `c ≤ y`, the decay factor at height `y` splits off a uniform `n₀`-tail:
`exp(-2π(m+n₀)y) ≤ exp(-2πc·m) · exp(-2πc·n₀)`. Used for absolute summability.
-/
private lemma exp_neg_two_pi_natCast_add_le (m n₀ : ℕ) {c y : ℝ} (hy : c ≤ y) :
    rexp (-(2 * π) * (↑m + ↑n₀) * y) ≤ rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [Real.pi_pos, (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
    (Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀),
    mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 2 * π * (↑m + ↑n₀))]

/--
For `c ≤ y`, the `m`-part of the decay factor at height `y` is bounded by its value at the
reference height `c`, keeping the `n₀`-part at height `y`:
`exp(-2π(m+n₀)y) ≤ exp(-2πc·m) · exp(-2π·n₀·y)`. Used in the main norm estimate.
-/
private lemma exp_neg_two_pi_natCast_add_le_mul (m n₀ : ℕ) {c y : ℝ} (hy : c ≤ y) :
    rexp (-(2 * π) * (↑m + ↑n₀) * y) ≤ rexp (-(2 * π * c) * m) * rexp (-(2 * π) * n₀ * y) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [Real.pi_pos, (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
    (Nat.cast_nonneg n₀ : (0 : ℝ) ≤ n₀),
    mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 2 * π * ↑m)]

/--
The Fourier terms `m ↦ a_m · exp(2πi(m+n₀)w)` are absolutely summable at any height
`w.im ≥ c`, provided the coefficient bound `m ↦ ‖a_m‖ · exp(-2πc·m)` is summable.
-/
private lemma summable_norm_fourier_shift_term {a : ℕ → ℂ} (n₀ : ℕ) {c : ℝ} (w : ℂ)
    (hw : c ≤ w.im) (ha : Summable (fun m : ℕ ↦ ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) :
    Summable fun m : ℕ ↦ ‖a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * w)‖ := by
  refine .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
    (ha.mul_right (rexp (-(2 * π * c) * n₀)))
  rw [norm_mul, norm_exp, mul_re_two_pi_I_natCast]
  calc ‖a m‖ * rexp (-(2 * π) * (↑m + ↑n₀) * w.im)
      ≤ ‖a m‖ * (rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀)) :=
        mul_le_mul_of_nonneg_left (exp_neg_two_pi_natCast_add_le m n₀ hw) (norm_nonneg (a m))
    _ = ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π * c) * n₀) := by ring

/--
If `F` has a Fourier expansion `∑_{m≥0} a_m exp(2πi(m+n₀)z)` with `n₀ > 0`,
and the coefficients are absolutely summable at height `im z = c`,
then `F = O(exp(-2π n₀ · im z))` at `atImInfty`.

The key bound is: for `im z ≥ c`,
  `‖F(z)‖ ≤ (∑_m ‖a_m‖ · exp(-2π c m)) · exp(-2π n₀ · im z)`
-/
lemma isBigO_atImInfty_of_fourier_shift
    {F : ℍ → ℂ} {a : ℕ → ℂ} {n₀ : ℕ} {c : ℝ} (_hn₀ : 0 < n₀) (_hc : 0 < c)
    (hF : ∀ z : ℍ, F z =
      ∑' m : ℕ, a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * (z : ℂ)))
    (ha : Summable (fun m : ℕ ↦ ‖a m‖ * rexp (-(2 * π * c) * (m : ℝ)))) :
    F =O[atImInfty] fun z : ℍ ↦ rexp (-(2 * π * (n₀ : ℝ)) * z.im) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨∑' m, ‖a m‖ * rexp (-(2 * π * c) * m), Filter.eventually_atImInfty.mpr
    ⟨c, fun z hz ↦ ?_⟩⟩
  rw [hF z, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hexp_re (m : ℕ) :
      (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z).re = -(2 * π) * (m + n₀) * z.im :=
    mul_re_two_pi_I_natCast m n₀ z
  have hsum_norms := summable_norm_fourier_shift_term n₀ (z : ℂ) hz ha
  have hsum_norms' : Summable fun m ↦ ‖a m‖ * rexp (-(2 * π) * (m + n₀) * z.im) := by
    convert hsum_norms with m
    rw [norm_mul, norm_exp, hexp_re]
  calc ‖∑' m, a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖
      ≤ ∑' m, ‖a m * cexp (2 * π * I * ((m + n₀ : ℕ) : ℂ) * z)‖ :=
        norm_tsum_le_tsum_norm hsum_norms
    _ = ∑' m, ‖a m‖ * rexp (-(2 * π) * (m + n₀) * z.im) := by
        simp only [norm_mul, norm_exp, hexp_re]
    _ ≤ ∑' m, ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π) * n₀ * z.im) := by
        refine Summable.tsum_le_tsum (fun m ↦ ?_) hsum_norms'
          (ha.mul_right (rexp (-(2 * π) * n₀ * z.im)))
        calc ‖a m‖ * rexp (-(2 * π) * (↑m + ↑n₀) * z.im)
            ≤ ‖a m‖ * (rexp (-(2 * π * c) * m) * rexp (-(2 * π) * n₀ * z.im)) :=
              mul_le_mul_of_nonneg_left (exp_neg_two_pi_natCast_add_le_mul m n₀ hz)
                (norm_nonneg (a m))
          _ = ‖a m‖ * rexp (-(2 * π * c) * m) * rexp (-(2 * π) * n₀ * z.im) := by ring
    _ = (∑' m, ‖a m‖ * rexp (-(2 * π * c) * m)) * rexp (-(2 * π) * n₀ * z.im) := tsum_mul_right
    _ = _ := by ring_nf

