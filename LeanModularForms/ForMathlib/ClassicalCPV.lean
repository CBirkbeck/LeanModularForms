/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Homotopy.Basic
import LeanModularForms.ForMathlib.PiecewiseC1PathOn

/-!
# Basic Definitions for Complex Analysis with Principal Values

Core definitions for piecewise C¹ curves, Cauchy principal value integrals,
and generalized winding numbers following Hungerbühler–Wasem.

## Main definitions

* `PiecewiseC1Curve`: a continuous curve `γ : [a, b] → ℂ` that is `C¹` away from a finite
  partition of the interval.
* `PiecewiseC1Immersion`: a piecewise `C¹` curve with nonzero derivative (one-sided limits
  at partition points are nonzero).
* `cauchyPrincipalValue'`: the Cauchy principal value of `∮_γ f(z) dz` excluding
  `ε`-neighbourhoods of a singularity `z₀`.
* `generalizedWindingNumber'`: the winding number of `γ` around `z₀` defined via the
  Cauchy principal value.
* `CurvesHomotopic` / `CurvesHomotopicAvoiding`: homotopy of curves relative to endpoints,
  optionally avoiding a singularity.

## Main results

* `intervalIntegrable_of_piecewise_continuousOn_bounded`: a piecewise continuous bounded
  function is interval integrable.
* `hasDerivWithinAt_zero_of_deriv_zero_off_finite`: if `f` is continuous on `[a, b]` and
  has zero derivative off a finite set, then its right derivative vanishes everywhere on
  `[a, b)`.
* `continuousWithinAt_integral_of_dominated_piecewise`: dominated convergence for
  parametric integrals over a piecewise continuous family.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- A piecewise continuously differentiable curve `γ : [a, b] → ℂ`, `C¹` on each
subinterval between partition points. Layers an Icc-style `partition` (endpoints included)
on top of an inherited `PiecewiseC1PathOn a b hab x y` whose partition is Ioo-style. -/
structure PiecewiseC1Curve where
  /-- Left endpoint of the parameter interval. -/
  a : ℝ
  /-- Right endpoint of the parameter interval. -/
  b : ℝ
  /-- Source value `γ(a)`. -/
  x : ℂ
  /-- Target value `γ(b)`. -/
  y : ℂ
  /-- The parameter interval is non-degenerate. -/
  hab : a < b
  /-- Underlying piecewise C¹ path on `[a, b]` from `x` to `y`. -/
  toPiecewiseC1PathOn : PiecewiseC1PathOn a b hab x y
  /-- The Icc-style partition (with endpoints `a, b` included). -/
  partition : Finset ℝ
  /-- The partition lies inside `[a, b]`. -/
  partition_subset : (partition : Set ℝ) ⊆ Icc a b
  /-- Both endpoints `a` and `b` belong to the partition. -/
  endpoints_in_partition : a ∈ partition ∧ b ∈ partition
  /-- The Icc-style partition is the inherited Ioo-style one with endpoints adjoined. -/
  partition_eq : partition = insert a (insert b toPiecewiseC1PathOn.partition)

namespace PiecewiseC1Curve

/-- The underlying function `ℝ → ℂ` of a piecewise `C¹` curve. -/
def toFun (γ : PiecewiseC1Curve) : ℝ → ℂ := γ.toPiecewiseC1PathOn.toFun

instance : CoeFun PiecewiseC1Curve fun _ ↦ ℝ → ℂ where coe := toFun

theorem continuous_toFun (γ : PiecewiseC1Curve) :
    ContinuousOn γ.toFun (Icc γ.a γ.b) := γ.toPiecewiseC1PathOn.continuous_toFun

private theorem notMem_innerPartition_of_notMem_partition (γ : PiecewiseC1Curve) {t : ℝ}
    (htn : t ∉ γ.partition) : t ∉ γ.toPiecewiseC1PathOn.partition := fun h_in => htn <| by
  rw [γ.partition_eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h_in)

/-- Differentiability off the (Icc-style) partition. -/
theorem smooth_off_partition (γ : PiecewiseC1Curve) :
    ∀ t ∈ Icc γ.a γ.b, t ∉ γ.partition → DifferentiableAt ℝ γ.toFun t := fun t ht htn => by
  have h_ne_a : t ≠ γ.a := fun h => htn (h ▸ γ.endpoints_in_partition.1)
  have h_ne_b : t ≠ γ.b := fun h => htn (h ▸ γ.endpoints_in_partition.2)
  exact γ.toPiecewiseC1PathOn.differentiable_off t
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h_ne_a), lt_of_le_of_ne ht.2 h_ne_b⟩
    (γ.notMem_innerPartition_of_notMem_partition htn)

theorem deriv_continuous_off_partition (γ : PiecewiseC1Curve) :
    ∀ t ∈ Ioo γ.a γ.b, t ∉ γ.partition → ContinuousAt (deriv γ.toFun) t := fun t ht htn =>
  γ.toPiecewiseC1PathOn.deriv_continuous_off t ht
    (γ.notMem_innerPartition_of_notMem_partition htn)

/-- **Smart constructor** from the legacy Icc-style field set. Reconstructs the underlying
`PiecewiseC1PathOn` by carving the partition's interior `partition.erase a |>.erase b`. -/
def ofIccPartition (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b) (partition : Finset ℝ)
    (partition_subset : (partition : Set ℝ) ⊆ Icc a b)
    (endpoints_in_partition : a ∈ partition ∧ b ∈ partition)
    (continuous_toFun : ContinuousOn toFun (Icc a b))
    (smooth_off_partition : ∀ t ∈ Icc a b, t ∉ partition → DifferentiableAt ℝ toFun t)
    (deriv_continuous_off_partition : ∀ t ∈ Ioo a b, t ∉ partition →
      ContinuousAt (deriv toFun) t) : PiecewiseC1Curve := by
  classical
  let openPart : Finset ℝ := (partition.erase a).erase b
  have h_eq : partition = insert a (insert b openPart) := by
    ext s
    by_cases h_a : s = a
    · simp [h_a, endpoints_in_partition.1]
    by_cases h_b : s = b
    · simp [h_b, endpoints_in_partition.2]
    simp [openPart, Finset.mem_insert, Finset.mem_erase, h_a, h_b]
  have h_sub : (openPart : Set ℝ) ⊆ Ioo a b := fun t ht => by
    obtain ⟨h_ne_b, ht'⟩ := Finset.mem_erase.mp ht
    obtain ⟨h_ne_a, h_in⟩ := Finset.mem_erase.mp ht'
    have h_icc := partition_subset h_in
    exact ⟨lt_of_le_of_ne h_icc.1 (Ne.symm h_ne_a), lt_of_le_of_ne h_icc.2 h_ne_b⟩
  have h_not : ∀ {t : ℝ}, t ∈ Ioo a b → t ∉ openPart → t ∉ partition :=
    fun {t} ht htn h_in => htn <| Finset.mem_erase.mpr ⟨ne_of_lt ht.2,
      Finset.mem_erase.mpr ⟨(ne_of_lt ht.1).symm, h_in⟩⟩
  exact
    { a := a, b := b, hab := hab, x := toFun a, y := toFun b
      toPiecewiseC1PathOn :=
        { toFun := toFun, source := rfl, target := rfl
          continuous_toFun := continuous_toFun
          partition := openPart, partition_subset := h_sub
          differentiable_off := fun t ht htn =>
            smooth_off_partition t (Ioo_subset_Icc_self ht) (h_not ht htn)
          deriv_continuous_off := fun t ht htn =>
            deriv_continuous_off_partition t ht (h_not ht htn) }
      partition := partition
      partition_subset := partition_subset
      endpoints_in_partition := endpoints_in_partition
      partition_eq := h_eq }

@[simp] theorem ofIccPartition_toFun (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (part : Finset ℝ) (h1 h2 h3 h4 h5) :
    (PiecewiseC1Curve.ofIccPartition toFun a b hab part h1 h2 h3 h4 h5).toFun = toFun := rfl

@[simp] theorem ofIccPartition_a (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (part : Finset ℝ) (h1 h2 h3 h4 h5) :
    (PiecewiseC1Curve.ofIccPartition toFun a b hab part h1 h2 h3 h4 h5).a = a := rfl

@[simp] theorem ofIccPartition_b (toFun : ℝ → ℂ) (a b : ℝ) (hab : a < b)
    (part : Finset ℝ) (h1 h2 h3 h4 h5) :
    (PiecewiseC1Curve.ofIccPartition toFun a b hab part h1 h2 h3 h4 h5).b = b := rfl

end PiecewiseC1Curve

/-- A closed curve has γ(a) = γ(b). -/
def PiecewiseC1Curve.IsClosed (γ : PiecewiseC1Curve) : Prop :=
  γ.toFun γ.a = γ.toFun γ.b

/-- A piecewise `C¹` immersion: a piecewise `C¹` curve whose derivative is nonzero and
admits nonzero one-sided limits at every partition point. -/
structure PiecewiseC1Immersion extends PiecewiseC1Curve where
  /-- The derivative is nonzero off the partition. -/
  deriv_ne_zero : ∀ t ∈ Icc a b, t ∉ partition → deriv toPiecewiseC1PathOn.toFun t ≠ 0
  /-- At every interior partition point the left limit of the derivative is nonzero. -/
  left_deriv_limit : ∀ p ∈ partition, a < p →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toPiecewiseC1PathOn.toFun) (𝓝[<] p) (𝓝 L)
  /-- At every interior partition point the right limit of the derivative is nonzero. -/
  right_deriv_limit : ∀ p ∈ partition, p < b →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toPiecewiseC1PathOn.toFun) (𝓝[>] p) (𝓝 L)

/-- The Cauchy principal value integrand at cutoff ε. -/
def cauchyPrincipalValueIntegrand' (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (z₀ : ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

@[simp]
theorem cauchyPrincipalValueIntegrand'_of_gt {f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {ε : ℝ} {t : ℝ}
    (h : ε < ‖γ t - z₀‖) :
    cauchyPrincipalValueIntegrand' f γ z₀ ε t = f (γ t) * deriv γ t := by
  simp only [cauchyPrincipalValueIntegrand', if_pos h]

@[simp]
theorem cauchyPrincipalValueIntegrand'_of_le {f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {ε : ℝ} {t : ℝ}
    (h : ‖γ t - z₀‖ ≤ ε) :
    cauchyPrincipalValueIntegrand' f γ z₀ ε t = 0 := by
  simp only [cauchyPrincipalValueIntegrand', if_neg (not_lt.mpr h)]

/-- The Cauchy principal value of ∮_γ f(z) dz, excluding ε-neighborhoods of z₀. -/
def cauchyPrincipalValue' (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε ↦
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/-- The Cauchy principal value exists if the limit exists. -/
def CauchyPrincipalValueExists' (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (fun ε ↦
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
    (𝓝[>] 0) (𝓝 L)

/-- The generalized winding number of γ around z₀, defined via principal value.
`n_{z₀}(γ) = (1/2πi) · PV ∮_γ dz/(z - z₀)`. -/
def generalizedWindingNumber' (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * cauchyPrincipalValue' (·⁻¹) (fun t ↦ γ t - z₀) a b 0

/-- Two curves are homotopic relative to endpoints. -/
def CurvesHomotopic (Γ γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = Γ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (a, s) = H (a, 0) ∧ H (b, s) = H (b, 0))

/-- Homotopy avoiding a point z₀. -/
def CurvesHomotopicAvoiding (Γ γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = Γ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (a, s) = z₀ ∧ H (b, s) = z₀) ∧
    (∀ t ∈ Ioo a b, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀)

private theorem aestronglyMeasurable_of_continuousOn_off_finite
    {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ}
    (hf_cont : ContinuousOn f ((Icc a b) \ P)) :
    AEStronglyMeasurable f (volume.restrict (Icc a b)) := by
  have h_union : Icc a b =
      (Icc a b \ (P : Set ℝ)) ∪ ((P : Set ℝ) ∩ Icc a b) := by
    rw [Set.inter_comm, Set.diff_union_inter]
  rw [h_union, aestronglyMeasurable_union_iff]
  constructor
  · exact hf_cont.aestronglyMeasurable
      (measurableSet_Icc.diff (Finset.measurableSet P))
  · rw [Measure.restrict_zero_set
      ((Finset.finite_toSet P |>.inter_of_left (Icc a b)).measure_zero _)]
    exact aestronglyMeasurable_zero_measure f

/-- A piecewise continuous bounded function is interval integrable. -/
theorem intervalIntegrable_of_piecewise_continuousOn_bounded
    {f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} (M : ℝ)
    (hab : a ≤ b)
    (hf_cont : ContinuousOn f ((Icc a b) \ P))
    (hf_bound : ∀ t ∈ Icc a b, ‖f t‖ ≤ M) :
    IntervalIntegrable f volume a b := by
  have hf_int : IntegrableOn f (Icc a b) volume :=
    ⟨aestronglyMeasurable_of_continuousOn_off_finite hf_cont,
     MeasureTheory.HasFiniteIntegral.restrict_of_bounded M
       (by rw [Real.volume_Icc]
           exact ENNReal.ofReal_lt_top)
       (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
           exact hf_bound t ht)⟩
  rw [← uIcc_of_le hab] at hf_int
  exact hf_int.intervalIntegrable

private theorem exists_min_above_in_finite_union
    (P : Finset ℝ) (t b : ℝ) (ht_lt_b : t < b) :
    ∃ s_min : ℝ, t < s_min ∧ s_min ≤ b ∧
      (∀ x ∈ Ioo t s_min, x ∉ ({b} ∪ (P : Set ℝ))) := by
  let S : Set ℝ := {b} ∪ (P : Set ℝ)
  let S_above : Set ℝ := {s ∈ S | t < s}
  have hS_above_finite : S_above.Finite :=
    ((Set.finite_singleton b).union (Finset.finite_toSet P)).subset fun _ hs ↦ hs.1
  have hne : hS_above_finite.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact ⟨b, by simp [S_above, S, ht_lt_b]⟩
  set s_min := hS_above_finite.toFinset.min' hne
  have hs_min_in : s_min ∈ S_above :=
    (Set.Finite.mem_toFinset _).mp (Finset.min'_mem _ hne)
  have hs_min_le : ∀ s ∈ S_above, s_min ≤ s :=
    fun s hs ↦ Finset.min'_le _ s ((Set.Finite.mem_toFinset _).mpr hs)
  exact ⟨s_min, hs_min_in.2,
    hs_min_le b ⟨Set.mem_union_left _ rfl, ht_lt_b⟩,
    fun x hx hxS ↦ by linarith [hs_min_le x ⟨hxS, hx.1⟩, hx.2]⟩

private theorem eq_on_Ioo_of_deriv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b t s_min : ℝ}
    (ht : t ∈ Ico a b) (ht_lt_s : t < s_min)
    (hf_cont : ContinuousOn f (Icc a b))
    (h_diff : DifferentiableOn ℝ f (Ioo t s_min))
    (h_dz : ∀ x ∈ Ioo t s_min, deriv f x = 0)
    (h_smin_le_b : s_min ≤ b) :
    ∀ x ∈ Ioo t s_min, f x = f t := by
  have h_mid : (t + s_min) / 2 ∈ Ioo t s_min := ⟨by linarith, by linarith⟩
  have h_eq_mid : ∀ x ∈ Ioo t s_min, f x = f ((t + s_min) / 2) :=
    fun _ hx ↦ IsOpen.is_const_of_deriv_eq_zero
      isOpen_Ioo isPreconnected_Ioo h_diff h_dz hx h_mid
  have h_cont_Ioo : ContinuousWithinAt f (Ioo t s_min) t :=
    (hf_cont.continuousWithinAt (Ico_subset_Icc_self ht)).mono
      fun _ hx ↦ ⟨(lt_of_le_of_lt ht.1 hx.1).le, (lt_of_lt_of_le hx.2 h_smin_le_b).le⟩
  have : (𝓝[Ioo t s_min] t).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt ht_lt_s)]
    exact ⟨le_refl t, ht_lt_s.le⟩
  have h_ft : f t = f ((t + s_min) / 2) := tendsto_nhds_unique
    (h_cont_Ioo.tendsto.congr' (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact h_eq_mid y hy))
    tendsto_const_nhds
  intro x hx
  rw [h_ft]
  exact h_eq_mid x hx

/-- If f is continuous on [a,b], differentiable on (a,b)\P with f'=0 there,
then f has zero right derivative at every point of [a,b). -/
theorem hasDerivWithinAt_zero_of_deriv_zero_off_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (P : Finset ℝ)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, t ∉ P →
      DifferentiableAt ℝ f t)
    (hf_deriv_zero : ∀ t ∈ Ioo a b, t ∉ P →
      deriv f t = 0) :
    ∀ t ∈ Ico a b, HasDerivWithinAt f 0 (Ici t) t := by
  intro t ht
  obtain ⟨s_min, ht_lt_s, h_smin_le_b, h_avoid⟩ :=
    exists_min_above_in_finite_union P t b ht.2
  have h_Ioo_sub : Ioo t s_min ⊆ Ioo a b := fun x hx ↦
    ⟨lt_of_le_of_lt ht.1 hx.1, lt_of_lt_of_le hx.2 h_smin_le_b⟩
  have h_not_P : ∀ x ∈ Ioo t s_min, x ∉ (P : Set ℝ) :=
    fun x hx hxP ↦ h_avoid x hx (Set.mem_union_right _ hxP)
  have h_eq : ∀ x ∈ Ioo t s_min, f x = f t :=
    eq_on_Ioo_of_deriv_zero ht ht_lt_s hf_cont
      (fun x hx ↦ (hf_diff x (h_Ioo_sub hx)
        (h_not_P x hx)).differentiableWithinAt)
      (fun x hx ↦ hf_deriv_zero x (h_Ioo_sub hx) (h_not_P x hx))
      h_smin_le_b
  rw [hasDerivWithinAt_iff_tendsto_slope]
  exact tendsto_nhds_of_eventually_eq (by
    filter_upwards [show Ioo t s_min ∈ 𝓝[Ici t \ {t}] t by
      rw [mem_nhdsWithin]
      exact ⟨Iio s_min, isOpen_Iio, ht_lt_s,
        fun x ⟨hx_Iio, hx_Ici_diff⟩ ↦
          ⟨lt_of_le_of_ne hx_Ici_diff.1
            (Ne.symm hx_Ici_diff.2), hx_Iio⟩⟩]
      with x hx
    simp [slope, h_eq x hx])

/-- Dominated convergence for the parametric integral `x ↦ ∫ t in a..b, F x t` along a
filter restricted to `S`. -/
theorem continuousWithinAt_integral_of_dominated_piecewise
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {F : X → ℝ → ℂ} {x₀ : X} {a b : ℝ} {S : Set X} {M : ℝ}
    (hab : a ≤ b)
    (hF_meas : ∀ x ∈ S, AEStronglyMeasurable (F x) (volume.restrict (Icc a b)))
    (hF_bound : ∀ x ∈ S, ∀ t ∈ Icc a b, ‖F x t‖ ≤ M)
    (hF_cont : ∀ᵐ t ∂volume.restrict (Icc a b), ContinuousWithinAt (fun x ↦ F x t) S x₀) :
    ContinuousWithinAt (fun x ↦ ∫ t in a..b, F x t) S x₀ := by
  have h_uIoc_sub : Set.uIoc a b ⊆ Icc a b := uIoc_of_le hab ▸ Ioc_subset_Icc_self
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ ↦ M)
  · filter_upwards [self_mem_nhdsWithin (s := S)] with x hx
    exact (hF_meas x hx).mono_set h_uIoc_sub
  · filter_upwards [self_mem_nhdsWithin (s := S)] with x hx
    exact .of_forall fun t ht ↦ hF_bound x hx t (h_uIoc_sub ht)
  · exact intervalIntegrable_const
  · exact MeasureTheory.ae_imp_of_ae_restrict
      (MeasureTheory.ae_restrict_of_ae_restrict_of_subset h_uIoc_sub hF_cont)

end
