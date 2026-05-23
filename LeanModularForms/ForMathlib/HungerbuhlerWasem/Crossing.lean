/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.LaurentExtraction
import LeanModularForms.ForMathlib.HungerbuhlerWasem.SectorCancellation
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingCPV
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingHigherOrder
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistence
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistenceMulti
import LeanModularForms.ForMathlib.HungerbuhlerWasem.LocalCutoffs
import LeanModularForms.ForMathlib.HungerbuhlerWasem.MultiPoleDCT
import LeanModularForms.ForMathlib.CrossingAnalysis
import LeanModularForms.ForMathlib.PaperPwC1ImmersionInvariance

/-!
# Per-pole CPV composition (T-GL-01)

For each pole `s ∈ S`, the CPV of the polar part `decomp.polarPart s` along
`γ` equals `2πi · w(γ, s) · residue f s` — when γ crosses `s` transversely
(witnessed by a `SingleCrossingData γ s`) and the higher-order Laurent
contributions vanish (which is the conclusion of T-SC-01 under condition (B)).

The proof composes three pieces:

* T-CC-01 (`cpv_simplePole_at_crossing`) for the simple pole `a₀ / (z − s)`
  — this contributes the `2πi · w · residue` term, because `a₀` is exactly
  `decomp.coeff s ⟨0, _⟩ = residue f s`.
* T-SC-01 (`hasCauchyPVOn_singleton_pow_of_conditionB_assembled`, packaged
  per-term) for the higher-order Laurent terms `aₖ / (z − s)^(k+1)`,
  `k ≥ 1` — these contribute zero under condition (B). We take the per-term
  vanishing as a hypothesis here (rather than building it out in this file).
* Three small algebraic helpers (`HasCauchyPV.add`, `HasCauchyPV.zero_fun`,
  `HasCauchyPV.finset_sum`, `HasCauchyPV.congr_pointwise`) that the public
  CPV API in `CauchyPrincipalValue.lean` does not currently provide.

## Main results

* `HungerbuhlerWasem.HasCauchyPV.add` — additivity of CPV.
* `HungerbuhlerWasem.HasCauchyPV.zero_fun` — `HasCauchyPV 0 γ z₀ 0`.
* `HungerbuhlerWasem.HasCauchyPV.finset_sum` — finite-sum form.
* `HungerbuhlerWasem.HasCauchyPV.congr_pointwise` — congruence-rewrite via
  pointwise equality off the singularity.
* `HungerbuhlerWasem.cpv_polarPart_at_pole_under_conditions` — the headline
  theorem.
-/

open Filter Topology Set Complex MeasureTheory
open scoped Real

noncomputable section

namespace HungerbuhlerWasem

variable {x y : ℂ}

/-- Additivity of `HasCauchyPV`: if both `f` and `g` have CPVs along `γ` at `z₀` (with
limits `L₁` and `L₂`) and their cutoff integrands are interval integrable for each
`ε > 0`, then `f + g` has CPV `L₁ + L₂`. -/
theorem HasCauchyPV.add {f g : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ L₁ L₂ : ℂ}
    (hf : HasCauchyPV f γ z₀ L₁) (hg : HasCauchyPV g γ z₀ L₂)
    (hfi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrand f γ.toPath.extend z₀ ε t) volume 0 1)
    (hgi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrand g γ.toPath.extend z₀ ε t) volume 0 1) :
    HasCauchyPV (fun z => f z + g z) γ z₀ (L₁ + L₂) := by
  simp only [HasCauchyPV] at hf hg ⊢
  have heq : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrand (fun z => f z + g z) γ.toPath.extend z₀ ε t) =ᶠ[𝓝[>] 0]
      (fun ε => (∫ t in (0 : ℝ)..1, cpvIntegrand f γ.toPath.extend z₀ ε t) +
        (∫ t in (0 : ℝ)..1, cpvIntegrand g γ.toPath.extend z₀ ε t)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h_pt : (fun t => cpvIntegrand (fun z => f z + g z) γ.toPath.extend z₀ ε t) =
        (fun t => cpvIntegrand f γ.toPath.extend z₀ ε t +
          cpvIntegrand g γ.toPath.extend z₀ ε t) := by
      funext t
      simp only [cpvIntegrand]
      split_ifs <;> ring
    rw [h_pt]
    exact intervalIntegral.integral_add (hfi ε hε) (hgi ε hε)
  exact (hf.add hg).congr' heq.symm

/-- The Cauchy principal value of the zero function is zero. -/
theorem HasCauchyPV.zero_fun {γ : PiecewiseC1Path x y} {z₀ : ℂ} :
    HasCauchyPV (fun _ => (0 : ℂ)) γ z₀ 0 := by
  simp only [HasCauchyPV]
  refine Tendsto.congr (f₁ := fun _ => (0 : ℂ)) ?_ tendsto_const_nhds
  intro ε
  have h_zero : (fun t => cpvIntegrand (fun _ : ℂ => (0 : ℂ))
      γ.toPath.extend z₀ ε t) = fun _ => (0 : ℂ) := by
    funext t
    simp only [cpvIntegrand]
    split_ifs <;> simp
  rw [h_zero]
  exact intervalIntegral.integral_zero.symm

/-- Congruence rewrite for `HasCauchyPV` via pointwise equality off the singularity:
if `f z = g z` for all `z ≠ z₀`, then `HasCauchyPV f γ z₀ L` implies
`HasCauchyPV g γ z₀ L`. -/
theorem HasCauchyPV.congr_pointwise {f g : ℂ → ℂ} {γ : PiecewiseC1Path x y}
    {z₀ L : ℂ} (h : HasCauchyPV f γ z₀ L) (hfg : ∀ z, z ≠ z₀ → f z = g z) :
    HasCauchyPV g γ z₀ L := by
  simp only [HasCauchyPV] at h ⊢
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [cpvIntegrand]
  split_ifs with hgt
  · have h_ne : γ.toPath.extend t ≠ z₀ := by
      intro heq
      rw [heq, sub_self, norm_zero] at hgt
      linarith
    rw [hfg _ h_ne]
  · rfl

/-- Finite sum of `HasCauchyPV`: if each `f i` has CPV `L i` along `γ` at `z₀` (with
cutoff integrability), the sum `∑ i ∈ T, f i` has CPV `∑ i ∈ T, L i`. -/
theorem HasCauchyPV.finset_sum {ι : Type*} [DecidableEq ι] (T : Finset ι)
    {γ : PiecewiseC1Path x y} {z₀ : ℂ} {f : ι → ℂ → ℂ} {L : ι → ℂ}
    (hf : ∀ i ∈ T, HasCauchyPV (f i) γ z₀ (L i))
    (hfi : ∀ i ∈ T, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrand (f i) γ.toPath.extend z₀ ε t) volume 0 1) :
    HasCauchyPV (fun z => ∑ i ∈ T, f i z) γ z₀ (∑ i ∈ T, L i) := by
  induction T using Finset.induction_on with
  | empty => simpa [Finset.sum_empty] using HasCauchyPV.zero_fun (γ := γ) (z₀ := z₀)
  | @insert a T' hia ih =>
    have h_T'_int : ∀ ε > 0, IntervalIntegrable
        (fun t => cpvIntegrand (fun z => ∑ i ∈ T', f i z) γ.toPath.extend z₀ ε t)
        volume 0 1 := fun ε hε => by
      have h_pt : (fun t => cpvIntegrand (fun z => ∑ i ∈ T', f i z)
          γ.toPath.extend z₀ ε t) =
          (fun t => ∑ i ∈ T', cpvIntegrand (f i) γ.toPath.extend z₀ ε t) := by
        funext t
        simp only [cpvIntegrand]
        split_ifs
        · rw [Finset.sum_mul]
        · exact Finset.sum_const_zero.symm
      rw [h_pt, show (fun t => ∑ i ∈ T', cpvIntegrand (f i) γ.toPath.extend z₀ ε t) =
          ∑ i ∈ T', fun t => cpvIntegrand (f i) γ.toPath.extend z₀ ε t from
          funext fun _ => (Finset.sum_apply _ _ _).symm]
      exact IntervalIntegrable.sum T'
        (fun i hi => hfi i (Finset.mem_insert_of_mem hi) ε hε)
    rw [show (fun z => ∑ i ∈ insert a T', f i z) = (fun z => f a z + ∑ i ∈ T', f i z) from
        funext fun _ => Finset.sum_insert hia, Finset.sum_insert hia]
    exact HasCauchyPV.add (hf a (Finset.mem_insert_self a T'))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfi i (Finset.mem_insert_of_mem hi)))
      (hfi a (Finset.mem_insert_self a T')) h_T'_int

/-- **Asymmetric variant of T-GL-01.** Per-pole CPV at a transverse crossing
using `AsymmetricSingleCrossingData`. This admits curves with `‖L_-‖ ≠ ‖L_+‖`
at the crossing — i.e., asymmetric chord-to-tangent constants which the
symmetric form cannot express. -/
theorem cpv_polarPart_at_pole_under_conditions_asymmetric
    {γ : PiecewiseC1Path x y} {s : ℂ} (D : AsymmetricSingleCrossingData γ s)
    {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} (hs : s ∈ S)
    (decomp : PolarPartDecomposition f S U)
    (h_higher : ∀ k : Fin (decomp.order s), k.val ≥ 1 →
      HasCauchyPV (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)) γ s 0)
    (h_term_int : ∀ k : Fin (decomp.order s), ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrand (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1))
        γ.toPath.extend s ε t) volume 0 1) :
    HasCauchyPV (decomp.polarPart s) γ s
      (2 * ↑Real.pi * I * generalizedWindingNumber γ s * residue f s) := by
  classical
  set N : ℕ := decomp.order s
  set a : Fin N → ℂ := decomp.coeff s
  set w : ℂ := generalizedWindingNumber γ s
  set term : Fin N → ℂ → ℂ := fun k z => a k / (z - s) ^ (k.val + 1)
  set L : Fin N → ℂ := fun k =>
    if k.val = 0 then 2 * ↑Real.pi * I * w * a k else 0
  have h_each : ∀ k : Fin N, HasCauchyPV (term k) γ s (L k) := fun k => by
    by_cases hk : k.val = 0
    · have h_term_eq : term k = fun z => a k / (z - s) := by
        funext z; simp only [term, show (k.val + 1 : ℕ) = 1 from by omega, pow_one]
      rw [h_term_eq, show L k = 2 * ↑Real.pi * I * w * a k from by simp [L, hk]]
      exact cpv_simplePole_at_crossing_asymmetric D (a k)
    · rw [show L k = (0 : ℂ) from by simp [L, hk]]
      exact h_higher k (by omega)
  have h_sum := HasCauchyPV.finset_sum (Finset.univ : Finset (Fin N))
    (γ := γ) (z₀ := s) (f := term) (L := L)
    (fun k _ => h_each k) (fun k _ => h_term_int k)
  have h_sum_eq : (∑ k : Fin N, L k) = 2 * ↑Real.pi * I * w * residue f s := by
    rw [decomp.residue_eq s hs]
    by_cases h_pos : 0 < N
    · rw [dif_pos h_pos, Finset.sum_eq_single (⟨0, h_pos⟩ : Fin N)]
      · change (if ((⟨0, h_pos⟩ : Fin N) : ℕ) = 0 then
          2 * ↑Real.pi * I * w * a ⟨0, h_pos⟩ else 0) =
            2 * ↑Real.pi * I * w * decomp.coeff s ⟨0, h_pos⟩
        rw [if_pos rfl]
      · intro k _ hk
        have hk_ne : k.val ≠ 0 := fun h_eq => hk (Fin.ext h_eq)
        change (if (k : ℕ) = 0 then _ else (0 : ℂ)) = 0
        rw [if_neg hk_ne]
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [dif_neg h_pos, mul_zero]
      exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
  rw [← h_sum_eq]
  exact HasCauchyPV.congr_pointwise h_sum
    fun z hz => (decomp.polarPart_eq s hs z hz).symm

/-- Per-pole CPV at a transverse crossing: for a pole `s ∈ S` with Laurent decomposition
recorded in `decomp`, given a `SingleCrossingData γ s` plus per-term CPV vanishing of the
higher-order Laurent terms (which holds under condition (B) via T-SC-01), the polar
part `decomp.polarPart s` has Cauchy principal value `2πi · w · residue f s` along `γ`
at `s`. Derived from the asymmetric variant via `SingleCrossingData.toAsymmetric`. -/
theorem cpv_polarPart_at_pole_under_conditions
    {γ : PiecewiseC1Path x y} {s : ℂ} (D : SingleCrossingData γ s)
    {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} (hs : s ∈ S)
    (decomp : PolarPartDecomposition f S U)
    (h_higher : ∀ k : Fin (decomp.order s), k.val ≥ 1 →
      HasCauchyPV (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)) γ s 0)
    (h_term_int : ∀ k : Fin (decomp.order s), ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrand (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1))
        γ.toPath.extend s ε t) volume 0 1) :
    HasCauchyPV (decomp.polarPart s) γ s
      (2 * ↑Real.pi * I * generalizedWindingNumber γ s * residue f s) :=
  cpv_polarPart_at_pole_under_conditions_asymmetric D.toAsymmetric hs decomp
    h_higher h_term_int

/-- Pointwise equality of `cpvIntegrandOn S f` with the cutoff integrand of
the polar-part decomposition `analyticRemainder + ∑ polarPart s`. The cutoff
zeroes both sides when `∃ s ∈ S, ‖γ(t) - s‖ ≤ ε`; otherwise `γ(t) ∈ U \ S`
and `decomp.decomp` applies. -/
private theorem cpvIntegrandOn_eq_of_decomp
    {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ}
    (decomp : PolarPartDecomposition f S U)
    {γ : PiecewiseC1Path x x} {t : ℝ} (ht : γ.toPath.extend t ∈ U) {ε : ℝ}
    (hε_pos : 0 < ε) :
    cpvIntegrandOn S f γ.toPath.extend ε t =
      cpvIntegrandOn S
        (fun z => decomp.analyticRemainder z + ∑ s ∈ S, decomp.polarPart s z)
        γ.toPath.extend ε t := by
  classical
  by_cases h : ∃ s ∈ S, ‖γ.toPath.extend t - s‖ ≤ ε
  · rw [cpvIntegrandOn_of_exists_le h, cpvIntegrandOn_of_exists_le h]
  · have h_far : ∀ s ∈ S, ε < ‖γ.toPath.extend t - s‖ := by
      intro s hs
      exact lt_of_not_ge fun h_le => h ⟨s, hs, h_le⟩
    have hγ_notS : γ.toPath.extend t ∉ (↑S : Set ℂ) := by
      intro h_mem
      have h_ne_zero : ε < ‖γ.toPath.extend t - γ.toPath.extend t‖ :=
        h_far _ (Finset.mem_coe.mp h_mem)
      simp at h_ne_zero
      linarith
    have hγ_in : γ.toPath.extend t ∈ U \ (↑S : Set ℂ) := ⟨ht, hγ_notS⟩
    have h_decomp := decomp.decomp _ hγ_in
    rw [cpvIntegrandOn_of_forall_gt h_far, cpvIntegrandOn_of_forall_gt h_far,
      h_decomp]

/-- **Hungerbühler–Wasem Theorem 3.3 — compositional crossing form.**

For `f` with a `PolarPartDecomposition` over `S ⊆ U` and a closed γ
null-homologous in `U` (which may cross poles of any order), the multi-point
Cauchy principal value of `∮f` along `γ` equals
`∑ s ∈ S, 2πi · w(γ, s) · residue f s`.

Per-pole CPV witnesses for each polar part — typically obtained from
`cpv_polarPart_at_pole_under_conditions` (T-GL-01) — are supplied as data.
The analytic-remainder CPV and integrability are derived internally from
`analyticRemainder_hasCauchyPVOn_zero` and
`cpvIntegrandOn_diff_intervalIntegrable`. The avoidance form
`residueTheorem_avoidance` is the special case where the per-pole witnesses
come from `hasCauchyPVOn_of_avoids`.

This is the *compositional* form: it consumes a `PolarPartDecomposition` and
per-pole CPV witnesses as data. -/
theorem residueTheorem_crossing_compositional
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U)
    (h_polar_cpv : ∀ s ∈ S, HasCauchyPVOn S (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s)) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γP t ∈ U := h_null.image_subset
  have h_rem_cpv : HasCauchyPVOn S decomp.analyticRemainder γP 0 :=
    HungerbuhlerWasem.analyticRemainder_hasCauchyPVOn_zero hU_open hU_ne
      hS_in_U γ h_null decomp
  have h_rem_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S decomp.analyticRemainder
        γP.toPath.extend ε t) volume 0 1 :=
    fun ε _ => HungerbuhlerWasem.cpvIntegrandOn_diff_intervalIntegrable γ S
      decomp.analyticRemainder_diff hγ_in_U ε
  have h_polar_int : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (decomp.polarPart s)
        γP.toPath.extend ε t) volume 0 1 :=
    fun s hs ε hε =>
      HungerbuhlerWasem.cpvIntegrandOn_polarPart_intervalIntegrable γ
        hS_in_U decomp hs h_null hε
  have h_sum_polar : HasCauchyPVOn S
      (fun z => ∑ s ∈ S, decomp.polarPart s z) γP
      (∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γP s *
        residue f s) :=
    HasCauchyPVOn.finset_sum S h_polar_cpv h_polar_int
  have h_sum_polar_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => ∑ s ∈ S, decomp.polarPart s z)
        γP.toPath.extend ε t) volume 0 1 := by
    intro ε hε
    have h_pt : (fun t => cpvIntegrandOn S
        (fun z => ∑ s ∈ S, decomp.polarPart s z) γP.toPath.extend ε t) =
        (fun t => ∑ s ∈ S, cpvIntegrandOn S (decomp.polarPart s)
          γP.toPath.extend ε t) := by
      funext t
      simp only [cpvIntegrandOn]
      split_ifs
      · exact Finset.sum_const_zero.symm
      · rw [Finset.sum_mul]
    rw [h_pt, show (fun t => ∑ s ∈ S, cpvIntegrandOn S (decomp.polarPart s)
        γP.toPath.extend ε t) = ∑ s ∈ S, fun t => cpvIntegrandOn S (decomp.polarPart s)
          γP.toPath.extend ε t from funext fun _ => (Finset.sum_apply _ _ _).symm]
    exact IntervalIntegrable.sum S (fun s hs => h_polar_int s hs ε hε)
  have h_decomp : HasCauchyPVOn S
      (fun z => decomp.analyticRemainder z + ∑ s ∈ S, decomp.polarPart s z) γP
      (0 + ∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γP s * residue f s) :=
    HasCauchyPVOn.add h_rem_cpv h_sum_polar h_rem_int h_sum_polar_int
  rw [zero_add] at h_decomp
  simp only [HasCauchyPVOn] at h_decomp ⊢
  refine h_decomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (zero_le_one' ℝ)] at ht
  exact (cpvIntegrandOn_eq_of_decomp decomp (hγ_in_U t ht) hε).symm

/-- **Per-pole CPV at an uncrossed pole.** When γ avoids the pole `s`, the polar
part `decomp.polarPart s` is regular along γ, and DCT gives that the multi-point
CPV equals the contour integral of the polar part along γ. The contour integral
in turn equals `2πi · w · res f s` by the avoidance computation
(`residueTheorem_avoidance` per-pole step). -/
theorem cpv_polarPart_at_uncrossed_pole
    {U : Set ℂ} (_hU_open : IsOpen U) (_hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U)
    (s : ℂ) (hs : s ∈ S)
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) :
    HasCauchyPVOn S (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := avoids_delta_bound γP s h_avoid
  have h_deriv_int : IntervalIntegrable (deriv γP.toPath.extend)
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
    refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  have h_cont_inv_each : ∀ k : Fin (decomp.order s), ContinuousOn
      (fun t => decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1))
      (Icc (0 : ℝ) 1) := fun k => ContinuousOn.div continuousOn_const
      ((γP.toPath.continuous_extend.continuousOn.sub continuousOn_const).pow _)
      fun t ht hzero =>
        h_avoid t ht (sub_eq_zero.mp (pow_eq_zero_iff (Nat.succ_pos _).ne' |>.mp hzero))
  have h_pp_curve_cont : ContinuousOn
      (fun t => decomp.polarPart s (γP.toPath.extend t)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    have h_sum_cont : ContinuousOn
        (fun t => ∑ k : Fin (decomp.order s),
          decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1))
        (Icc (0 : ℝ) 1) :=
      continuousOn_finset_sum _ fun k _ => h_cont_inv_each k
    refine h_sum_cont.congr fun t ht => ?_
    change decomp.polarPart s (γP.toPath.extend t) =
      ∑ k : Fin (decomp.order s),
        decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1)
    exact decomp.polarPart_eq s hs (γP.toPath.extend t) (h_avoid t ht)
  have h_full : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP)
      MeasureTheory.volume 0 1 :=
    h_deriv_int.continuousOn_mul h_pp_curve_cont
  have h_contourInt :
      γP.contourIntegral (decomp.polarPart s) =
        2 * ↑Real.pi * I * generalizedWindingNumber γP s * residue f s := by
    have h_higherOrder_int_each : ∀ k : Fin (decomp.order s), k.val ≥ 1 →
        IntervalIntegrable
          (fun t => decomp.coeff s k /
            (γP.toPath.extend t - s) ^ (k.val + 1) *
            deriv γP.toPath.extend t) volume 0 1 :=
      fun k _ => h_deriv_int.continuousOn_mul ((h_cont_inv_each k).mono
        (by rw [uIcc_of_le (zero_le_one' ℝ)]))
    have h_polarPart_curve : ∀ t ∈ Icc (0 : ℝ) 1,
        decomp.polarPart s (γP.toPath.extend t) =
          ∑ k : Fin (decomp.order s),
            decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1) :=
      fun t ht => decomp.polarPart_eq s hs (γP.toPath.extend t) (h_avoid t ht)
    have h_int_eq : γP.contourIntegral (decomp.polarPart s) =
        γP.contourIntegral (fun z => ∑ k : Fin (decomp.order s),
          decomp.coeff s k / (z - s) ^ (k.val + 1)) := by
      simp only [PiecewiseC1Path.contourIntegral]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le (zero_le_one' ℝ)] at ht
      change decomp.polarPart s (γP.toPath.extend t) * deriv γP.toPath.extend t =
        (∑ k : Fin (decomp.order s),
          decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1)) *
            deriv γP.toPath.extend t
      rw [h_polarPart_curve t ht]
    rw [h_int_eq]
    have h_int_each : ∀ k : Fin (decomp.order s), IntervalIntegrable
        (PiecewiseC1Path.contourIntegrand
          (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)) γP) volume 0 1 := fun k =>
      h_deriv_int.continuousOn_mul ((h_cont_inv_each k).mono
        (by rw [uIcc_of_le (zero_le_one' ℝ)]))
    rw [PiecewiseC1Path.contourIntegral_finset_sum Finset.univ _ γP
      (fun k _ => h_int_each k)]
    by_cases h_order_pos : 0 < decomp.order s
    · have h_split := Finset.sum_eq_single_of_mem
        (s := (Finset.univ : Finset (Fin (decomp.order s))))
        (a := ⟨0, h_order_pos⟩)
        (f := fun k : Fin (decomp.order s) =>
          γP.contourIntegral (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)))
        (Finset.mem_univ _)
        (fun k _ hk_ne => by
          have hk_ge_1 : k.val ≥ 1 := by
            have : k.val ≠ 0 := fun h => hk_ne (Fin.ext h)
            omega
          have hk_succ_ge_2 : 2 ≤ k.val + 1 := by omega
          exact contourIntegral_higherOrder_eq_zero_of_avoids γP h_avoid hk_succ_ge_2
            _ (h_higherOrder_int_each k hk_ge_1))
      rw [h_split]
      simp only [zero_add, pow_one]
      have h_residue_eq : decomp.coeff s ⟨0, h_order_pos⟩ = residue f s :=
        ((decomp.residue_eq s hs).trans (dif_pos h_order_pos)).symm
      rw [h_residue_eq]
      set w := generalizedWindingNumber γP s with hw_def
      have h_winding_int_eq :
          γP.contourIntegral (fun z => (z - s)⁻¹) = 2 * ↑Real.pi * I * w := by
        have h1 := hasCauchyPV_of_avoids (f := fun z => (z - s)⁻¹) (γ := γP) (z₀ := s)
          ⟨δ, hδ_pos, fun t ht => hδ_bound t ht⟩
        unfold generalizedWindingNumber at hw_def
        rw [h1.cauchyPV_eq] at hw_def
        have h2pi_ne : (2 * (↑Real.pi : ℂ) * I) ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero
            (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
        rw [hw_def, mul_inv_cancel_left₀ h2pi_ne]
      have h_const_factor : γP.contourIntegral (fun z => residue f s / (z - s)) =
          residue f s * γP.contourIntegral (fun z => (z - s)⁻¹) := by
        rw [show (fun z => residue f s / (z - s)) =
            (fun z => residue f s * (z - s)⁻¹) from funext fun z => div_eq_mul_inv _ _]
        exact PiecewiseC1Path.contourIntegral_smul (residue f s) _ γP
      rw [h_const_factor, h_winding_int_eq]
      ring
    · rw [show residue f s = 0 by
            have h := decomp.residue_eq s hs; rwa [dif_neg h_order_pos] at h, mul_zero]
      exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)
  have h_meas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun t => cpvIntegrandOn S (decomp.polarPart s)
        γP.toPath.extend ε t)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h_full_int := HungerbuhlerWasem.cpvIntegrandOn_polarPart_intervalIntegrable γ
      hS_in_U decomp hs h_null hε
    exact h_full_int.aestronglyMeasurable_restrict_uIoc
  have h_bound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Set.uIoc (0 : ℝ) 1 →
      ‖cpvIntegrandOn S (decomp.polarPart s) γP.toPath.extend ε x‖ ≤
        ‖PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP x‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine MeasureTheory.ae_of_all _ fun t _ => ?_
    rw [HungerbuhlerWasem.cpvIntegrandOn_eq_indicator_compl γP S
      (decomp.polarPart s) ε t]
    by_cases ht_in : t ∈ (HungerbuhlerWasem.cpv_badSet γP S ε)ᶜ
    · rw [Set.indicator_of_mem ht_in]
    · rw [Set.indicator_of_notMem ht_in, norm_zero]; exact norm_nonneg _
  have h_pointwise_raw :=
    HungerbuhlerWasem.cpvIntegrandOn_tendsto_contourIntegrand_ae γ S
    (decomp.polarPart s)
  have h_pointwise : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      Tendsto (fun ε => cpvIntegrandOn S (decomp.polarPart s)
          γP.toPath.extend ε x) (𝓝[>] 0)
        (𝓝 (PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP x)) := by
    rwa [MeasureTheory.ae_restrict_iff' measurableSet_uIoc] at h_pointwise_raw
  have h_dct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP t‖)
    h_meas h_bound h_full.norm h_pointwise
  unfold HasCauchyPVOn
  rw [show (2 * ↑Real.pi * I *
      generalizedWindingNumber γP s * residue f s : ℂ) =
      γP.contourIntegral (decomp.polarPart s) from h_contourInt.symm]
  exact h_dct

/-- **Asymmetric variant** of `cpv_polarPart_at_crossed_pole_hasCauchyPV`
(T-BR-04b). Single-point CPV at a crossed pole using
`AsymmetricSingleCrossingData`, which admits asymmetric crossings where
the chord-to-tangent constants on the two sides differ. -/
theorem cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric
    {U : Set ℂ} {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x)
    (_h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U)
    (s : ℂ) (hs : s ∈ S)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t = s → t = t₀)
    (h_t₀_off_partition :
      t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition)
    (D : AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s)
    (n : ℕ) (h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ n)
    (hn1 : 1 ≤ n) (h_order_le_n : decomp.order s ≤ n)
    (h_angle : ∀ (k : Fin (decomp.order s)), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∃ m : ℤ, ((k.val : ℝ)) * Real.pi = (m : ℝ) * (2 * Real.pi)) :
    HasCauchyPV (decomp.polarPart s) γ.toPwC1Immersion.toPiecewiseC1Path s
      (2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_term_int : ∀ k : Fin (decomp.order s), ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrand (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1))
        γP.toPath.extend s ε t) volume 0 1 := fun k ε hε => by
    have h := HungerbuhlerWasem.cpvIntegrandOn_singleMonomial_intervalIntegrable
      γ (S := {s}) (Finset.mem_singleton.mpr rfl)
      (decomp.coeff s k) (k.val + 1) hε
    rwa [show (fun t => cpvIntegrandOn ({s} : Finset ℂ)
        (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)) γP.toPath.extend ε t) =
      (fun t => cpvIntegrand (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1))
        γP.toPath.extend s ε t) from
      funext fun _ => (cpvIntegrand_eq_cpvIntegrandOn_singleton (z₀ := s)).symm] at h
  have h_higher : ∀ k : Fin (decomp.order s), k.val ≥ 1 →
      HasCauchyPV (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)) γP s 0 := fun k hk => by
    have hk_succ_ge_2 : 2 ≤ k.val + 1 := by omega
    have hk_succ_le_n : k.val + 1 ≤ n := by have := k.isLt; omega
    by_cases h_zero : decomp.coeff s k = 0
    · rw [show (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)) = fun _ => (0 : ℂ) from
        funext fun _ => by rw [h_zero, zero_div]]
      exact hasCauchyPV_of_hasCauchyPVOn_singleton (HasCauchyPVOn.zero_fun (γ := γP)
        (S := {s}))
    · exact hasCauchyPV_of_hasCauchyPVOn_singleton
        (HungerbuhlerWasem.hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB
          γ ht₀ h_at h_unique h_t₀_off_partition
          hk_succ_ge_2 hk_succ_le_n hn1 h_flat
          (show ∃ m : ℤ, (((k.val + 1) - 1 : ℕ) : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi) by
            rw [show ((k.val + 1) - 1 : ℕ) = k.val from by omega]; exact h_angle k hk h_zero)
          (decomp.coeff s k))
  exact cpv_polarPart_at_pole_under_conditions_asymmetric D hs decomp h_higher h_term_int

/-- **Single-point CPV at a crossed pole, using condition (B).**

Given a `SingleCrossingData` for `γ` at the pole `s` (the residual oracle from
`h_geometry`) plus condition (B) at the crossing parameter, produce the
single-point CPV `HasCauchyPV (decomp.polarPart s) γ s value`. Derived from the
asymmetric variant via `SingleCrossingData.toAsymmetric`. -/
theorem cpv_polarPart_at_crossed_pole_hasCauchyPV
    {U : Set ℂ} {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U)
    (s : ℂ) (hs : s ∈ S)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t = s → t = t₀)
    (h_t₀_off_partition :
      t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition)
    (D : SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s)
    (n : ℕ) (h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ n)
    (hn1 : 1 ≤ n) (h_order_le_n : decomp.order s ≤ n)
    (h_angle : ∀ (k : Fin (decomp.order s)), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∃ m : ℤ, ((k.val : ℝ)) * Real.pi = (m : ℝ) * (2 * Real.pi)) :
    HasCauchyPV (decomp.polarPart s) γ.toPwC1Immersion.toPiecewiseC1Path s
      (2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric hS_in_U γ h_null decomp s hs
    ht₀ h_at h_unique h_t₀_off_partition D.toAsymmetric n h_flat hn1 h_order_le_n
    h_angle

/-- **Corner-friendly variant** of `cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric`
(T-BR-Y10b). Drops `h_t₀_off_partition` in exchange for explicit one-sided
derivative limits `L_-`, `L_+` and the per-coefficient angle equation
`h_B_k : (L_+/‖L_+‖)^k = ((-L_-)/‖L_-‖)^k` (derived from condition (B) at
corner via `angle_compat_of_condB_anywhere` + `h_B_of_angle_compat_corner`).

This delegates the higher-order vanishing to
`hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`, which
handles corner crossings via the relaxed FTC over the countable corner
exception set. -/
theorem cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric_corner
    {U : Set ℂ} {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x)
    (_h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U)
    (s : ℂ) (hs : s ∈ S)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t = s → t = t₀)
    {L_minus L_plus : ℂ} (hL_minus_ne : L_minus ≠ 0) (hL_plus_ne : L_plus ≠ 0)
    (hL_right : Tendsto
      (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
      (𝓝[>] t₀) (𝓝 L_plus))
    (hL_left : Tendsto
      (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
      (𝓝[<] t₀) (𝓝 L_minus))
    (D : AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s)
    (n : ℕ) (h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ n)
    (hn1 : 1 ≤ n) (h_order_le_n : decomp.order s ≤ n)
    (h_B : ∀ (k : Fin (decomp.order s)), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      (L_plus / (↑‖L_plus‖ : ℂ)) ^ k.val =
      ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ k.val) :
    HasCauchyPV (decomp.polarPart s) γ.toPwC1Immersion.toPiecewiseC1Path s
      (2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_term_int : ∀ k : Fin (decomp.order s), ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrand (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1))
        γP.toPath.extend s ε t) volume 0 1 := fun k ε hε => by
    have h := HungerbuhlerWasem.cpvIntegrandOn_singleMonomial_intervalIntegrable
      γ (S := {s}) (Finset.mem_singleton.mpr rfl)
      (decomp.coeff s k) (k.val + 1) hε
    rwa [show (fun t => cpvIntegrandOn ({s} : Finset ℂ)
        (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)) γP.toPath.extend ε t) =
      (fun t => cpvIntegrand (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1))
        γP.toPath.extend s ε t) from
      funext fun _ => (cpvIntegrand_eq_cpvIntegrandOn_singleton (z₀ := s)).symm] at h
  have h_higher : ∀ k : Fin (decomp.order s), k.val ≥ 1 →
      HasCauchyPV (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)) γP s 0 := fun k hk => by
    have hk_succ_ge_2 : 2 ≤ k.val + 1 := by omega
    have hk_succ_le_n : k.val + 1 ≤ n := by have := k.isLt; omega
    by_cases h_zero : decomp.coeff s k = 0
    · rw [show (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)) = fun _ => (0 : ℂ) from
        funext fun _ => by rw [h_zero, zero_div]]
      exact hasCauchyPV_of_hasCauchyPVOn_singleton (HasCauchyPVOn.zero_fun (γ := γP)
        (S := {s}))
    · exact hasCauchyPV_of_hasCauchyPVOn_singleton
        (HungerbuhlerWasem.hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner
          γ ht₀ h_at h_unique hL_minus_ne hL_plus_ne hL_right hL_left
          hk_succ_ge_2 hk_succ_le_n hn1 h_flat
          (show (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k.val + 1 - 1) =
              ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k.val + 1 - 1) by
            rw [show k.val + 1 - 1 = k.val from by omega]; exact h_B k hk h_zero)
          (decomp.coeff s k))
  exact cpv_polarPart_at_pole_under_conditions_asymmetric D hs decomp h_higher h_term_int

/-- **Lift: from `HasCauchyPV` to `HasCauchyPVOn S`** when γ avoids every other
pole in `S`. The cutoff sets `B_{s'}(ε)` for `s' ∈ S \ {s}` are eventually
empty as `ε → 0` (γ stays a positive distance from each `s'`). Hence the
multi-point cutoff integrand equals the singleton cutoff integrand for
`ε` smaller than the avoidance distance. -/
theorem hasCauchyPVOn_of_hasCauchyPV_of_avoid_other_poles
    {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {s : ℂ} {S : Finset ℂ} (_hs : s ∈ S)
    {L : ℂ} (h : HasCauchyPV f γ s L)
    (h_avoid_others : ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s') :
    HasCauchyPVOn S f γ L := by
  classical
  have h_S_erase_avoids : ∀ s' ∈ S.erase s, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s' := by
    intro s' hs' t ht
    have hne : s' ≠ s := Finset.ne_of_mem_erase hs'
    have hin : s' ∈ S := Finset.mem_of_mem_erase hs'
    exact h_avoid_others s' hin hne t ht
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    avoids_finset_delta_bound γ (S.erase s) h_S_erase_avoids
  have h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t =
        ∫ t in (0 : ℝ)..1, cpvIntegrand f γ.toPath.extend s ε t := by
    filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε_in
    have hε_pos : 0 < ε := hε_in.1
    have hε_lt : ε < δ := hε_in.2
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (zero_le_one' ℝ)] at ht
    have h_far_others : ∀ s' ∈ S.erase s, ε < ‖γ.toPath.extend t - s'‖ := by
      intro s' hs'
      exact lt_of_lt_of_le hε_lt (hδ_bound s' hs' t ht)
    by_cases h_near_s : ‖γ.toPath.extend t - s‖ ≤ ε
    · have h_S : ∃ s'' ∈ S, ‖γ.toPath.extend t - s''‖ ≤ ε := ⟨s, _hs, h_near_s⟩
      rw [cpvIntegrandOn_of_exists_le h_S, cpvIntegrand_of_le h_near_s]
    · push Not at h_near_s
      have h_far_S : ∀ s'' ∈ S, ε < ‖γ.toPath.extend t - s''‖ := by
        intro s'' hs''
        by_cases h_eq : s'' = s
        · rw [h_eq]; exact h_near_s
        · exact h_far_others s'' (Finset.mem_erase.mpr ⟨h_eq, hs''⟩)
      rw [cpvIntegrandOn_of_forall_gt h_far_S, cpvIntegrand_of_gt h_near_s]
  unfold HasCauchyPVOn
  unfold HasCauchyPV at h
  exact h.congr' (Filter.EventuallyEq.symm h_eq)

/-- **T-BR-Y1 helper.** Given `hCondA : SatisfiesConditionA' γ f S (decomp.order)`
and a crossing `γ t₀ = s` at an interior parameter, extract the data
`⟨n, 1 ≤ n, decomp.order s ≤ n, IsFlatOfOrder γ t₀ n⟩` previously supplied as
`h_flat_at_crossings`. The case-split on `decomp.order s` selects either the
condition-(A')-supplied flatness (when `decomp.order s ≥ 1`) or the automatic
order-1 flatness from `isFlatOfOrder_one` (when `decomp.order s = 0`). -/
private theorem flat_data_of_condA_at_crossing
    {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ}
    {γ : ClosedPwC1Immersion x}
    (decomp : PolarPartDecomposition f S U)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S (fun s => decomp.order s))
    {s : ℂ} (hs : s ∈ S) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s) :
    ∃ n : ℕ, 1 ≤ n ∧ decomp.order s ≤ n ∧
      IsFlatOfOrder γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ n := by
  have ht_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀
  have h_flat_d : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ (decomp.order s) :=
    hCondA s hs t₀ ht_Icc h_at ht₀
  by_cases h_pos : 1 ≤ decomp.order s
  · exact ⟨decomp.order s, h_pos, le_refl _, h_flat_d⟩
  · refine ⟨1, le_refl 1, by omega, ?_⟩
    exact isFlatOfOrder_one γ.toPwC1Immersion t₀ ht₀

/-- **Laurent polynomial uniqueness — vanishing form.**

If a finite Laurent polynomial `Σ k : Fin N, c k / (z - s)^(k+1)` is eventually
equal (in the punctured neighborhood of `s`) to an analytic function at `s`,
then all coefficients `c k` vanish.

We prove this by reverse induction on `N`: peel the highest-order coefficient
(`c_{N-1}`) by evaluating both sides of `(z - s)^N · LHS = (z - s)^N · g` at
`z = s`. The polynomial side at `z = s` equals `c_{N-1}` (only the `k = N-1`
term survives, as it has exponent 0); the analytic side equals `0^N · g(s) = 0`
when `N ≥ 1`. Hence `c_{N-1} = 0`. Induct down. -/
private theorem laurent_polynomial_zero_of_eventuallyEq_analytic :
    ∀ (N : ℕ) (c : Fin N → ℂ) {s : ℂ} {g : ℂ → ℂ}, AnalyticAt ℂ g s →
      (fun z => ∑ k : Fin N, c k / (z - s) ^ (k.val + 1)) =ᶠ[𝓝[≠] s] g →
      ∀ k : Fin N, c k = 0 := by
  classical
  intro N
  induction N with
  | zero =>
    intro c s g _ _ k
    exact absurd k.isLt (by omega)
  | succ N ih =>
    intro c s g hg h_eq
    set P : ℂ → ℂ := fun z => ∑ k : Fin (N + 1), c k * (z - s) ^ (N - k.val) with hP_def
    set Q : ℂ → ℂ := fun z => (z - s) ^ (N + 1) * g z with hQ_def
    have hP_an : AnalyticAt ℂ P s := by
      refine Finset.analyticAt_fun_sum _ fun k _ => ?_
      exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).pow _)
    have hQ_an : AnalyticAt ℂ Q s :=
      ((analyticAt_id.sub analyticAt_const).pow (N + 1)).mul hg
    have h_PQ_punc : P =ᶠ[𝓝[≠] s] Q := by
      filter_upwards [h_eq, self_mem_nhdsWithin] with z hz hz_ne
      have hz_sub : (z - s) ≠ 0 := sub_ne_zero.mpr hz_ne
      have h_lhs : P z = (z - s) ^ (N + 1) *
          (∑ k : Fin (N + 1), c k / (z - s) ^ (k.val + 1)) := by
        rw [hP_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk_le : k.val + 1 ≤ N + 1 := k.isLt
        have hpow : (z - s) ^ (N + 1) =
            (z - s) ^ (N - k.val) * (z - s) ^ (k.val + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [div_eq_mul_inv, hpow]
        have h_pow_ne : ((z - s) ^ (k.val + 1)) ≠ 0 := pow_ne_zero _ hz_sub
        field_simp
      rw [h_lhs, hz, hQ_def]
    have h_PQ_full : P =ᶠ[𝓝 s] Q :=
      (hP_an.frequently_eq_iff_eventually_eq hQ_an).mp h_PQ_punc.frequently
    have hPs : P s = c ⟨N, Nat.lt_succ_self _⟩ := by
      show (∑ k : Fin (N + 1), c k * (s - s) ^ (N - k.val)) =
        c ⟨N, Nat.lt_succ_self _⟩
      rw [sub_self, Finset.sum_eq_single (⟨N, Nat.lt_succ_self _⟩ : Fin (N + 1))
        (fun k _ hk => by
          have hk_lt : k.val < N := by
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp k.isLt) with h | h
            · exact h
            · exact absurd (Fin.ext h) hk
          rw [zero_pow (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hk_lt)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    have hcN_zero : c ⟨N, Nat.lt_succ_self _⟩ = 0 := by
      rw [← hPs, h_PQ_full.eq_of_nhds]
      show (s - s) ^ (N + 1) * g s = 0
      rw [sub_self, zero_pow (Nat.succ_ne_zero N), zero_mul]
    set c' : Fin N → ℂ := fun k => c k.castSucc
    have h_eq' : (fun z => ∑ k : Fin N, c' k / (z - s) ^ (k.val + 1)) =ᶠ[𝓝[≠] s] g := by
      filter_upwards [h_eq] with z hz
      rw [show ∑ k : Fin N, c' k / (z - s) ^ (k.val + 1) =
          ∑ k : Fin (N + 1), c k / (z - s) ^ (k.val + 1) from ?_]
      · exact hz
      rw [Fin.sum_univ_castSucc]
      have h_last : c (⟨N, Nat.lt_succ_self _⟩ : Fin (N+1)) /
          (z - s) ^ (N + 1) = 0 := by
        rw [hcN_zero, zero_div]
      have h_match : (Fin.last N : Fin (N+1)) = ⟨N, Nat.lt_succ_self _⟩ := rfl
      rw [h_match] at *
      simp [h_last, c']
    have ih_result : ∀ k : Fin N, c' k = 0 := ih c' hg h_eq'
    intro k
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp k.isLt) with hk | hk
    · have h_eq_cast : k = (⟨k.val, hk⟩ : Fin N).castSucc := by ext; rfl
      rw [h_eq_cast]
      exact ih_result ⟨k.val, hk⟩
    · have h_eq_last : k = ⟨N, Nat.lt_succ_self _⟩ := by ext; exact hk
      rw [h_eq_last]
      exact hcN_zero

/-- Auxiliary: a Laurent polynomial `Σ k : Fin N, c k / (z - s)^(k+1)` equals
its `(Fin (max N M))` extension (with zeros) at every `z ≠ s`. -/
private lemma laurent_sum_extend {N M : ℕ} (hNM : N ≤ M) (c : Fin N → ℂ)
    (s z : ℂ) (_hz : z ≠ s) :
    (∑ k : Fin N, c k / (z - s) ^ (k.val + 1)) =
      ∑ j : Fin M,
        (if hj : j.val < N then c ⟨j.val, hj⟩ else (0 : ℂ)) /
          (z - s) ^ (j.val + 1) := by
  classical
  have h_emb : Function.Injective (fun k : Fin N => (⟨k.val, lt_of_lt_of_le k.isLt hNM⟩ : Fin M)) := by
    intro a b hab; ext; exact Fin.mk.inj_iff.mp hab
  rw [show (∑ j : Fin M, (if hj : j.val < N then c ⟨j.val, hj⟩ else (0 : ℂ)) /
        (z - s) ^ (j.val + 1)) =
      ∑ j ∈ (Finset.univ : Finset (Fin M)).filter (fun j => j.val < N),
        (if hj : j.val < N then c ⟨j.val, hj⟩ else (0 : ℂ)) /
          (z - s) ^ (j.val + 1) from ?_]
  · have h_image : (Finset.univ : Finset (Fin N)).image
        (fun k => (⟨k.val, lt_of_lt_of_le k.isLt hNM⟩ : Fin M)) =
        (Finset.univ : Finset (Fin M)).filter (fun j => j.val < N) := by
      ext j
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rintro ⟨k, hk⟩; rw [← hk]; exact k.isLt
      · intro hj; exact ⟨⟨j.val, hj⟩, by ext; rfl⟩
    rw [← h_image, Finset.sum_image (fun a _ b _ h => h_emb h)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dif_pos k.isLt]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j.val < N
    · rw [if_pos hj]
    · rw [if_neg hj, dif_neg hj, zero_div]

/-- **Bridge: extended Laurent coefficients of two decompositions of the same `f`
must agree at every index.**

If `Σ k : Fin N₁, c₁ k / (z - s)^(k+1) - Σ k : Fin N₂, c₂ k / (z - s)^(k+1)`
is eventually equal (in `𝓝[≠] s`) to an analytic function at `s`, then for every
index `j`, the extended coefficients agree. -/
private theorem laurent_extended_coeff_eq_of_diff_analytic
    {N₁ N₂ : ℕ} (c₁ : Fin N₁ → ℂ) (c₂ : Fin N₂ → ℂ)
    {s : ℂ} {h : ℂ → ℂ} (hh : AnalyticAt ℂ h s)
    (h_diff : (fun z => (∑ k : Fin N₁, c₁ k / (z - s) ^ (k.val + 1)) -
                        (∑ k : Fin N₂, c₂ k / (z - s) ^ (k.val + 1))) =ᶠ[𝓝[≠] s] h) :
    ∀ j : ℕ,
      (if hj : j < N₁ then c₁ ⟨j, hj⟩ else (0 : ℂ)) =
      (if hj : j < N₂ then c₂ ⟨j, hj⟩ else (0 : ℂ)) := by
  classical
  set M : ℕ := max N₁ N₂ with hM_def
  set d : Fin M → ℂ := fun j =>
    (if hj : j.val < N₁ then c₁ ⟨j.val, hj⟩ else (0 : ℂ)) -
    (if hj : j.val < N₂ then c₂ ⟨j.val, hj⟩ else (0 : ℂ)) with hd_def
  have h_sum_eq : (fun z => ∑ j : Fin M, d j / (z - s) ^ (j.val + 1)) =ᶠ[𝓝[≠] s] h := by
    filter_upwards [h_diff, self_mem_nhdsWithin] with z hz hz_ne
    have hz_sub : z ≠ s := hz_ne
    have h_d_split : (∑ j : Fin M, d j / (z - s) ^ (j.val + 1)) =
        (∑ j : Fin M,
          (if hj : j.val < N₁ then c₁ ⟨j.val, hj⟩ else (0 : ℂ)) /
            (z - s) ^ (j.val + 1)) -
        (∑ j : Fin M,
          (if hj : j.val < N₂ then c₂ ⟨j.val, hj⟩ else (0 : ℂ)) /
            (z - s) ^ (j.val + 1)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hd_def, sub_div]
    rw [h_d_split,
      ← laurent_sum_extend (le_max_left N₁ N₂) c₁ s z hz_sub,
      ← laurent_sum_extend (le_max_right N₁ N₂) c₂ s z hz_sub]
    exact hz
  have hd_zero : ∀ j : Fin M, d j = 0 :=
    laurent_polynomial_zero_of_eventuallyEq_analytic M d hh h_sum_eq
  intro j
  by_cases hj_M : j < M
  · have hd_j_zero := hd_zero ⟨j, hj_M⟩
    rw [hd_def] at hd_j_zero
    exact sub_eq_zero.mp hd_j_zero
  · have hj_N1 : ¬ j < N₁ := fun h => hj_M (lt_of_lt_of_le h (le_max_left _ _))
    have hj_N2 : ¬ j < N₂ := fun h => hj_M (lt_of_lt_of_le h (le_max_right _ _))
    rw [dif_neg hj_N1, dif_neg hj_N2]

/-- **Corner-friendly form of `angle_compat_of_condB`** (T-BR-Y10b).
Drops the `h_t₀_off` hypothesis: returns the angle equation in terms of
`angleAtCrossing γ t₀ ht₀` directly, which is `π` at smooth points and
`arg L_+ - arg(-L_-)` at corner points. The caller is responsible for
interpreting the angle in the corner case (via
`h_B_of_angle_compat_corner`). -/
theorem angle_compat_of_condB_anywhere
    {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ} (hU_open : IsOpen U) (hS_in_U : ↑S ⊆ U)
    (γ : ClosedPwC1Immersion x)
    (decomp : PolarPartDecomposition f S U)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    {s : ℂ} (hs : s ∈ S) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at₀ : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s) :
    ∀ (k : Fin (decomp.order s)), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∃ m : ℤ, ((k.val : ℝ)) * angleAtCrossing γ.toPwC1Immersion t₀ ht₀ =
        (m : ℝ) * (2 * Real.pi) := by
  classical
  intro k hk hk_ne
  have ht_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀
  obtain ⟨N, a, g, hg, hf_eq, h_angles⟩ :=
    hCondB.laurent_compatible s hs t₀ ht_Icc h_at₀ ht₀
  set hOther : ℂ → ℂ := fun z =>
    g z - decomp.analyticRemainder z -
      ∑ s' ∈ S.erase s, decomp.polarPart s' z with hOther_def
  have h_arem_an : AnalyticAt ℂ decomp.analyticRemainder s :=
    decomp.analyticRemainder_diff.analyticAt
      (hU_open.mem_nhds (hS_in_U (Finset.mem_coe.mpr hs)))
  have h_otherPolar_an : AnalyticAt ℂ
      (fun z => ∑ s' ∈ S.erase s, decomp.polarPart s' z) s := by
    refine Finset.analyticAt_fun_sum _ fun s' hs' => ?_
    have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
    have hs'_in : s' ∈ S := (Finset.mem_erase.mp hs').2
    have h_polar_eq : ∀ᶠ z in 𝓝 s,
        decomp.polarPart s' z = ∑ k : Fin (decomp.order s'),
          decomp.coeff s' k / (z - s') ^ (k.val + 1) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds
        (show s ∈ ({s'}ᶜ : Set ℂ) from fun h_eq => hne h_eq.symm)] with z hz
      exact decomp.polarPart_eq s' hs'_in z hz
    have h_sum_an : AnalyticAt ℂ
        (fun z => ∑ k : Fin (decomp.order s'),
          decomp.coeff s' k / (z - s') ^ (k.val + 1)) s :=
      Finset.analyticAt_fun_sum _ fun k _ =>
        analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
          (pow_ne_zero _ (sub_ne_zero.mpr hne.symm))
    exact h_sum_an.congr (h_polar_eq.mono fun _ hz => hz.symm)
  have hOther_an : AnalyticAt ℂ hOther s :=
    (hg.sub h_arem_an).sub h_otherPolar_an
  have h_diff : (fun z => (∑ k : Fin (decomp.order s),
        decomp.coeff s k / (z - s) ^ (k.val + 1)) -
      (∑ k : Fin N, a k / (z - s) ^ (k.val + 1))) =ᶠ[𝓝[≠] s] hOther := by
    have h_other_S_closed : IsClosed (↑(S.erase s) : Set ℂ) :=
      (S.erase s).finite_toSet.isClosed
    filter_upwards [hf_eq, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hU_open.mem_nhds (hS_in_U (Finset.mem_coe.mpr hs))),
      nhdsWithin_le_nhds (h_other_S_closed.isOpen_compl.mem_nhds
        (show s ∉ (↑(S.erase s) : Set ℂ) from fun h_mem =>
          (Finset.mem_erase.mp (Finset.mem_coe.mp h_mem)).1 rfl))]
      with z hz hz_ne hz_U hz_not_other
    have hz_not_S : z ∉ (↑S : Set ℂ) := fun h_mem => by
      by_cases h_eq : z = s
      · exact hz_ne h_eq
      · exact hz_not_other (Finset.mem_coe.mpr
          (Finset.mem_erase.mpr ⟨h_eq, Finset.mem_coe.mp h_mem⟩))
    have h_decomp_z : f z = decomp.analyticRemainder z +
        ∑ s' ∈ S, decomp.polarPart s' z := decomp.decomp z ⟨hz_U, hz_not_S⟩
    have h_split : ∑ s' ∈ S, decomp.polarPart s' z =
        decomp.polarPart s z + ∑ s' ∈ S.erase s, decomp.polarPart s' z := by
      rw [← Finset.add_sum_erase _ _ hs]
    have h_pp_eq : decomp.polarPart s z =
        ∑ k : Fin (decomp.order s), decomp.coeff s k / (z - s) ^ (k.val + 1) :=
      decomp.polarPart_eq s hs z hz_ne
    show (∑ k : Fin (decomp.order s), decomp.coeff s k / (z - s) ^ (k.val + 1)) -
        (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
      g z - decomp.analyticRemainder z -
        ∑ s' ∈ S.erase s, decomp.polarPart s' z
    have h_combined : decomp.analyticRemainder z +
        (∑ s' ∈ S.erase s, decomp.polarPart s' z) +
        (∑ k : Fin (decomp.order s), decomp.coeff s k / (z - s) ^ (k.val + 1)) =
        g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) := by
      have h_full : f z = decomp.analyticRemainder z +
          (∑ s' ∈ S.erase s, decomp.polarPart s' z) + decomp.polarPart s z := by
        rw [h_decomp_z, h_split]; ring
      rw [← h_pp_eq]
      linear_combination -h_full + hz
    linear_combination h_combined
  have h_k_eq :=
    laurent_extended_coeff_eq_of_diff_analytic (decomp.coeff s) a hOther_an h_diff k.val
  rw [dif_pos k.isLt] at h_k_eq
  have h_eq : decomp.coeff s ⟨k.val, k.isLt⟩ = decomp.coeff s k := by congr
  by_cases hk_N : k.val < N
  · rw [dif_pos hk_N] at h_k_eq
    exact h_angles ⟨k.val, hk_N⟩ (by rw [← h_k_eq, h_eq]; exact hk_ne) hk
  · rw [dif_neg hk_N, h_eq] at h_k_eq
    exact absurd h_k_eq hk_ne

/-- **T-BR-Y1 helper.** Angle compatibility for `decomp.coeff` at a smooth crossing,
derived from condition (B). At an off-partition crossing the angle is `π`, so this
specialises `angle_compat_of_condB_anywhere`. -/
theorem angle_compat_of_condB
    {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ} (hU_open : IsOpen U) (hS_in_U : ↑S ⊆ U)
    (γ : ClosedPwC1Immersion x)
    (decomp : PolarPartDecomposition f S U)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    {s : ℂ} (hs : s ∈ S) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at₀ : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s)
    (h_t₀_off : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition) :
    ∀ (k : Fin (decomp.order s)), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∃ m : ℤ, ((k.val : ℝ)) * Real.pi = (m : ℝ) * (2 * Real.pi) := by
  have h_angle_α : angleAtCrossing γ.toPwC1Immersion t₀ ht₀ = Real.pi :=
    angleAtCrossing_smooth γ.toPwC1Immersion t₀ ht₀ h_t₀_off
  have h := angle_compat_of_condB_anywhere hU_open hS_in_U γ decomp hCondB hs ht₀ h_at₀
  intro k hk hk_ne
  have := h k hk hk_ne
  rwa [h_angle_α] at this

/-- **Asymmetric variant** of `cpv_polarPart_at_pole_from_conditions`. The
per-pole CPV witness when `h_geometry` supplies an
`AsymmetricSingleCrossingData`, admitting curves with `‖L_-‖ ≠ ‖L_+‖`. -/
theorem cpv_polarPart_at_pole_from_conditions_asymmetric
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (_hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => decomp.order s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (h_geometry : ∀ s ∈ S, ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s →
      t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition →
      AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s)
    (h_unique_cross : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t = s →
      ∃ t₀ ∈ Set.Ioo (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s ∧
        ∀ t' ∈ Icc (0 : ℝ) 1,
          γ.toPwC1Immersion.toPiecewiseC1Path t' = s → t' = t₀)
    (h_no_corner_crossings : ∀ s ∈ S, ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s →
      t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition)
    (h_avoid_others_per_pole : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s →
      ∀ t ∈ Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s')
    (s : ℂ) (hs : s ∈ S) :
    HasCauchyPVOn S (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  by_cases h_crossed : ∃ t ∈ Icc (0 : ℝ) 1, γP t = s
  · obtain ⟨t, ht, h_at⟩ := h_crossed
    obtain ⟨t₀, ht₀, h_at₀, h_unique_t₀⟩ := h_unique_cross s hs t ht h_at
    have h_t₀_off := h_no_corner_crossings s hs t₀ ht₀ h_at₀
    have D := h_geometry s hs t₀ ht₀ h_at₀ h_t₀_off
    obtain ⟨n, hn1, h_order_le_n, h_flat⟩ :=
      flat_data_of_condA_at_crossing decomp hCondA hs ht₀ h_at₀
    have h_angle_compat : ∀ (k : Fin (decomp.order s)), 1 ≤ k.val →
        decomp.coeff s k ≠ 0 →
        ∃ m : ℤ, ((k.val : ℝ)) * Real.pi = (m : ℝ) * (2 * Real.pi) :=
      angle_compat_of_condB hU_open hS_in_U γ decomp hCondB hs ht₀ h_at₀ h_t₀_off
    have h_HasCauchyPV := cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric
      hS_in_U γ h_null decomp s hs ht₀ h_at₀ h_unique_t₀ h_t₀_off D n h_flat
      hn1 h_order_le_n h_angle_compat
    exact hasCauchyPVOn_of_hasCauchyPV_of_avoid_other_poles hs h_HasCauchyPV
      (h_avoid_others_per_pole s hs)
  · push Not at h_crossed
    exact cpv_polarPart_at_uncrossed_pole hU_open hU_ne hS_in_U γ h_null decomp s hs
      h_crossed

/-- **Per-pole CPV at any pole, paper-faithful form (T-BR-04).**

For each pole `s ∈ S`, this theorem produces the per-pole CPV witness
`HasCauchyPVOn S (decomp.polarPart s) γ.toPiecewiseC1Path value`, the input
to the `h_polar_cpv` parameter of `residueTheorem_crossing_compositional`.
Derived from the asymmetric variant via `SingleCrossingData.toAsymmetric`. -/
theorem cpv_polarPart_at_pole_from_conditions
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => decomp.order s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (h_geometry : ∀ s ∈ S, ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s →
      t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition →
      SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s)
    (h_unique_cross : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t = s →
      ∃ t₀ ∈ Set.Ioo (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s ∧
        ∀ t' ∈ Icc (0 : ℝ) 1,
          γ.toPwC1Immersion.toPiecewiseC1Path t' = s → t' = t₀)
    (h_no_corner_crossings : ∀ s ∈ S, ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s →
      t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition)
    (h_avoid_others_per_pole : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s →
      ∀ t ∈ Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s')
    (s : ℂ) (hs : s ∈ S) :
    HasCauchyPVOn S (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  cpv_polarPart_at_pole_from_conditions_asymmetric hU_open hU_ne hS_in_U hf γ
    h_null decomp hCondA hCondB
    (fun s hs t₀ ht₀ h_at₀ h_off => (h_geometry s hs t₀ ht₀ h_at₀ h_off).toAsymmetric)
    h_unique_cross h_no_corner_crossings h_avoid_others_per_pole s hs

/-- **Crossing scenario** for `γ` relative to a finite pole set `S`.

The two constructors capture the natural cases:
- `avoidance`: γ avoids every pole in `S`.
- `oneCrossing t₀ s_cross …`: γ has a single, interior, off-partition
  crossing at `t₀` with pole `s_cross`, and avoids every other pole. -/
inductive CrossingScenario (γ : ClosedPwC1Immersion x) (S : Finset ℂ) : Type
  | avoidance :
      (∀ s ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) →
      CrossingScenario γ S
  | oneCrossing : ∀ (t₀ : ℝ) (s_cross : ℂ),
      t₀ ∈ Set.Ioo (0 : ℝ) 1 →
      s_cross ∈ S →
      γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s_cross →
      t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition →
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t = s_cross → t = t₀) →
      (∀ s' ∈ S, s' ≠ s_cross → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s') →
      CrossingScenario γ S

/-- **Per-pole geometric data for a crossing**, used as the optional payload in
`MultiCrossingScenario`. -/
structure PerPoleCrossData (γ : ClosedPwC1Immersion x) (s : ℂ) where
  /-- The unique parameter at which γ crosses `s`. -/
  t₀ : ℝ
  /-- The parameter is interior. -/
  ht₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1
  /-- γ at `t₀` is `s`. -/
  h_at : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s
  /-- `t₀` is off the legacy partition. -/
  h_off : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition
  /-- The crossing is unique. -/
  h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    γ.toPwC1Immersion.toPiecewiseC1Path t = s → t = t₀

/-- **Multi-crossing data for a single pole** (T-BR-Y6).

The Finset-of-crossings generalization of `PerPoleCrossData`: γ may cross
the pole `s` at *multiple* parameters `t₀ ∈ crossings`, each interior,
off-partition, with `γ(t₀) = s`. `h_complete` asserts that the finset
enumerates **all** crossings of `s` on `Icc 0 1` (no missed parameters).

For a `ClosedPwC1Immersion`, the set of crossings is automatically finite
(by transversality + compactness of `Icc 0 1`). This structure packages
that finiteness datum.

Compared to `PerPoleCrossData`, the uniqueness restriction is removed:
multiple `t₀ ∈ crossings` may hit the same pole. -/
structure MultiPoleCrossData (γ : ClosedPwC1Immersion x) (s : ℂ) where
  /-- Finite set of crossing parameters. -/
  crossings : Finset ℝ
  /-- Each crossing is interior. -/
  h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1
  /-- γ at each crossing parameter is `s`. -/
  h_at : ∀ t ∈ crossings, γ.toPwC1Immersion.toPiecewiseC1Path t = s
  /-- Each crossing is off the legacy partition. -/
  h_off : ∀ t ∈ crossings,
    t ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition
  /-- The crossings are complete: every parameter where γ = s is in the finset. -/
  h_complete : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    γ.toPwC1Immersion.toPiecewiseC1Path t = s → t ∈ crossings


/-- **Avoidance is the empty-crossings case of `MultiPoleCrossData`.** -/
noncomputable def MultiPoleCrossData.ofAvoidance
    {γ : ClosedPwC1Immersion x} {s : ℂ}
    (h_avoid : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) :
    MultiPoleCrossData γ s where
  crossings := ∅
  h_Ioo := by intro t ht; exact absurd ht (Finset.notMem_empty t)
  h_at := by intro t ht; exact absurd ht (Finset.notMem_empty t)
  h_off := by intro t ht; exact absurd ht (Finset.notMem_empty t)
  h_complete := by
    intro t ht h_eq
    exact absurd h_eq (h_avoid t ht)

/-- If `M.crossings` is empty, γ avoids `s` on `Icc 0 1`. -/
theorem MultiPoleCrossData.avoids_of_crossings_empty
    {γ : ClosedPwC1Immersion x} {s : ℂ} (M : MultiPoleCrossData γ s)
    (h_empty : M.crossings = ∅) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s := by
  intro t ht h_eq
  have h_mem := M.h_complete t ht h_eq
  rw [h_empty] at h_mem
  exact absurd h_mem (Finset.notMem_empty t)

/-- If `M.crossings` has exactly one element, we can extract a
`PerPoleCrossData`. -/
noncomputable def MultiPoleCrossData.toPerPole_of_card_one
    {γ : ClosedPwC1Immersion x} {s : ℂ} (M : MultiPoleCrossData γ s)
    (h_one : M.crossings.card = 1) :
    PerPoleCrossData γ s :=
  let t₀ := (Finset.card_eq_one.mp h_one).choose
  let h_eq := (Finset.card_eq_one.mp h_one).choose_spec
  { t₀ := t₀
    ht₀_Ioo := M.h_Ioo t₀ (by rw [h_eq]; exact Finset.mem_singleton_self t₀)
    h_at := M.h_at t₀ (by rw [h_eq]; exact Finset.mem_singleton_self t₀)
    h_off := M.h_off t₀ (by rw [h_eq]; exact Finset.mem_singleton_self t₀)
    h_unique := by
      intro t ht h_eq_at
      have h_mem := M.h_complete t ht h_eq_at
      rw [h_eq, Finset.mem_singleton] at h_mem
      exact h_mem }


/-- **Multi-crossing scenario for `γ` relative to a finite pole set `S`**.

For each `s ∈ S`, supply either:
- a proof that γ avoids `s` entirely (`avoidance s := ⟨ProofTerm⟩`), or
- per-pole crossing data: `PerPoleCrossData γ s`.

This generalizes `CrossingScenario.oneCrossing` to allow γ to cross multiple
poles. The multi-pole DCT lift handles the per-pole CPV-to-multi-CPV
transition without requiring γ to avoid the other poles. -/
structure MultiCrossingScenario (γ : ClosedPwC1Immersion x) (S : Finset ℂ) where
  /-- For each `s ∈ S`, either avoidance (left) or per-pole crossing data (right).
  Uses `PSum` since the left disjunct lives in `Prop` and the right in `Type`. -/
  data : ∀ s ∈ S,
    PSum
      (PLift (∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s))
      (PerPoleCrossData γ s)

/-- **Multi-pole multi-crossing scenario** (T-BR-Y6): for each `s ∈ S`,
supply a `MultiPoleCrossData γ s`. The single-pole avoidance case is the
empty `crossings` finset (cf. `MultiPoleCrossData.ofAvoidance`).

Compared to `MultiCrossingScenario`, this drops the per-pole uniqueness
requirement: γ may cross each pole at MULTIPLE parameters. -/
structure MultiPoleCrossScenario (γ : ClosedPwC1Immersion x) (S : Finset ℂ) where
  /-- For each `s ∈ S`, the multi-crossing data. -/
  data : ∀ s ∈ S, MultiPoleCrossData γ s

/-- **Hungerbühler–Wasem Theorem 3.3 — multi-crossings-per-pole form
(T-BR-Y6).**

Generalizes `residueTheorem_crossing_asymmetric_multiCrossing` to allow
γ to cross each pole at **multiple** parameters. Each pole `s` carries
a `MultiPoleCrossData γ s` enumerating the crossings.

For poles with `≥ 2` crossings, the user must supply a CPV witness for
the polar part (the `h_multi_cpv` hypothesis). For `≤ 1` crossings, the
witness is discharged automatically using the existing infrastructure. -/
private theorem residueTheorem_crossing_asymmetric_multiPole
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => (PolarPartDecomposition.ofMeromorphicWithCondB hU_open hS_in_U hf
        (γ := γ.toPwC1Immersion) hMero hCondB).order s))
    (scenario : MultiPoleCrossScenario γ S)
    /- Oracle: for poles with ≥ 2 crossings, a CPV witness for the polar part. -/
    (h_multi_cpv : ∀ (s : ℂ) (hs : s ∈ S),
      (scenario.data s hs).crossings.card ≥ 2 →
        HasCauchyPV
          ((PolarPartDecomposition.ofMeromorphicWithCondB hU_open hS_in_U hf
            (γ := γ.toPwC1Immersion) hMero hCondB).polarPart s)
          γ.toPwC1Immersion.toPiecewiseC1Path s
          (2 * ↑Real.pi * I *
            generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
              residue f s)) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set decomp : PolarPartDecomposition f S U :=
    PolarPartDecomposition.ofMeromorphicWithCondB hU_open hS_in_U hf
      (γ := γ.toPwC1Immersion) hMero hCondB
  refine residueTheorem_crossing_compositional hU_open hU_ne S hS_in_U f hf γ
    h_null decomp ?_
  intro s hs
  set M : MultiPoleCrossData γ s := scenario.data s hs
  by_cases h_card_zero : M.crossings.card = 0
  · have h_avoid : ∀ t ∈ Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s :=
      M.avoids_of_crossings_empty (Finset.card_eq_zero.mp h_card_zero)
    exact cpv_polarPart_at_uncrossed_pole hU_open hU_ne hS_in_U γ h_null decomp s hs
      h_avoid
  by_cases h_card_one : M.crossings.card = 1
  · let P : PerPoleCrossData γ s := M.toPerPole_of_card_one h_card_one
    have h_flat_data :=
      flat_data_of_condA_at_crossing (γ := γ) decomp hCondA hs P.ht₀_Ioo P.h_at
    have h_flat : IsFlatOfOrder
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend P.t₀ 1 :=
      h_flat_data.choose_spec.2.2.of_le h_flat_data.choose_spec.1
        γ.toPwC1Immersion.continuous.continuousAt
    have h_cpv_exists := hasCauchyPV_inv_sub_of_flat_one_full γ P.ht₀_Ioo P.h_at
      P.h_unique h_flat
    let D : AsymmetricSingleCrossingData
        γ.toPwC1Immersion.toPiecewiseC1Path s :=
      HungerbuhlerWasem.AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV
        γ P.ht₀_Ioo P.h_at P.h_unique P.h_off h_cpv_exists.choose_spec
    obtain ⟨n, hn1, h_order_le_n, h_flat_n⟩ :=
      flat_data_of_condA_at_crossing decomp hCondA hs P.ht₀_Ioo P.h_at
    exact MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole
      hS_in_U decomp γ hs h_null (cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric
        hS_in_U γ h_null decomp s hs P.ht₀_Ioo P.h_at P.h_unique P.h_off D n h_flat_n
        hn1 h_order_le_n
        (angle_compat_of_condB hU_open hS_in_U γ decomp hCondB hs P.ht₀_Ioo P.h_at P.h_off))
  have h_ge_two : M.crossings.card ≥ 2 := by
    have : 0 < M.crossings.card := Nat.pos_of_ne_zero h_card_zero
    omega
  exact MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole
    hS_in_U decomp γ hs h_null (h_multi_cpv s hs h_ge_two)


/-- **Auto-derived multi-pole crossing scenario** (T-BR-Y7).

Given a `ClosedPwC1Immersion γ` and a finite pole set `S` such that:
- γ's base point `x` is not a pole, and
- no pole crossing on the interior occurs at a partition point,

the multi-crossing scenario is built automatically from Proposition 2.2: the
crossing set `{t ∈ Icc 0 1 | γ(t) = s}` is finite, so it can be packaged as a
`MultiPoleCrossData γ s`. -/
noncomputable def MultiPoleCrossScenario.ofImmersion
    {γ : ClosedPwC1Immersion x} {S : Finset ℂ}
    (hx_notin_S : x ∉ (↑S : Set ℂ))
    (h_no_corner_crossings : ∀ s ∈ S, ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s →
      t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition) :
    MultiPoleCrossScenario γ S where
  data s hs := by
    classical
    have h0_ne : (γ.toPwC1Immersion : ℝ → ℂ) 0 ≠ s := by
      simp only [show (γ.toPwC1Immersion : ℝ → ℂ) 0 =
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 0 from rfl,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend_zero]
      exact fun h_eq => hx_notin_S (h_eq ▸ hs)
    have h1_ne : (γ.toPwC1Immersion : ℝ → ℂ) 1 ≠ s := by
      simp only [show (γ.toPwC1Immersion : ℝ → ℂ) 1 =
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 1 from rfl,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend_one]
      exact fun h_eq => hx_notin_S (h_eq ▸ hs)
    have hfin : Set.Finite (γ.toPwC1Immersion.crossingSet s) :=
      PwC1Immersion.crossingSet_finite γ.toPwC1Immersion s h0_ne h1_ne
    have h_to_Ioo : ∀ t ∈ Icc (0 : ℝ) 1, (γ.toPwC1Immersion : ℝ → ℂ) t = s →
        t ∈ Ioo (0 : ℝ) 1 := fun t h_in_Icc h_at_t =>
      ⟨lt_of_le_of_ne h_in_Icc.1 fun h_eq => h0_ne (h_eq ▸ h_at_t),
       lt_of_le_of_ne h_in_Icc.2 fun h_eq => h1_ne (h_eq.symm ▸ h_at_t)⟩
    refine
      { crossings := hfin.toFinset
        h_Ioo := fun t ht => h_to_Ioo t (hfin.mem_toFinset.mp ht).1 (hfin.mem_toFinset.mp ht).2
        h_at := fun t ht => (hfin.mem_toFinset.mp ht).2
        h_off := fun t ht =>
          let ht' := hfin.mem_toFinset.mp ht
          h_no_corner_crossings s hs t (h_to_Ioo t ht'.1 ht'.2) ht'.2
        h_complete := fun t ht h_eq => hfin.mem_toFinset.mpr ⟨ht, h_eq⟩ }


/-- **HW3.3 — `no_unique_constraint` form (T-BR-Y9).**

Drops `h_unique_cross` from `_no_basepoint_constraint` by exposing the multi-pole
CPV witness for the polar part as a single named oracle hypothesis
`h_multi_cpv_polar_part`. The oracle is required ONLY for poles `s ∈ S` where γ
has `≥ 2` crossings — for the typical setting (each pole crossed at most once),
the predicate is vacuous and the theorem applies unconditionally.

### Eliminating `h_unique_cross`

Compared to `_no_basepoint_constraint`, this theorem drops `h_unique_cross` and
replaces it with `h_multi_cpv_polar_part`, which is **vacuous when each pole is
crossed at most once** (the typical case). Net: callers with uniqueness lose one
hypothesis with no replacement (the `card ≤ 1` branch discharges the oracle
automatically); callers with genuine multi-crossings gain a clearly-named
residual that future tickets will discharge via per-window aggregation.

### Note on `hx_notin_S`

Without `h_unique_cross`, the `x ∈ S` branch is no longer auto-discharged. We
therefore keep `hx_notin_S` as a hypothesis, matching the `_full_spec` form. The
combined elimination (no `hx_notin_S` AND no `h_unique_cross`) requires a full
cyclic-shift reparametrization theorem, which is a separate follow-up. -/
theorem residueTheorem_crossing_no_basepoint_no_unique_constraint
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => (PolarPartDecomposition.ofMeromorphicWithCondB hU_open hS_in_U hf
        (γ := γ.toPwC1Immersion) hMero hCondB).order s))
    (hx_notin_S : x ∉ (↑S : Set ℂ))
    (h_no_corner_crossings : ∀ s ∈ S, ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s →
      t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition)
    /- **Per-pole multi-crossing CPV oracle.** For each pole `s ∈ S` with ≥ 2
       crossings (i.e., `(MultiPoleCrossScenario.ofImmersion ...).data s hs`
       has `crossings.card ≥ 2`), the CPV of `decomp.polarPart s` along γ at `s`
       equals the residue-theorem value. For `card ≤ 1`, this oracle is vacuous
       (the premise `≥ 2` fails). -/
    (h_multi_cpv_polar_part :
      ∀ (s : ℂ) (hs : s ∈ S),
        ((MultiPoleCrossScenario.ofImmersion (γ := γ) (S := S)
          hx_notin_S h_no_corner_crossings).data s hs).crossings.card ≥ 2 →
        HasCauchyPV
          ((PolarPartDecomposition.ofMeromorphicWithCondB hU_open hS_in_U hf
            (γ := γ.toPwC1Immersion) hMero hCondB).polarPart s)
          γ.toPwC1Immersion.toPiecewiseC1Path s
          (2 * ↑Real.pi * I *
            generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
              residue f s)) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set scenario := MultiPoleCrossScenario.ofImmersion (γ := γ) (S := S)
    hx_notin_S h_no_corner_crossings
  exact residueTheorem_crossing_asymmetric_multiPole hU_open hU_ne hS_in_U hf γ
    h_null hMero hCondB hCondA scenario h_multi_cpv_polar_part

/-- **Bridge: corner-angle compat to corner `h_B`.** Given the condition (B)
angle equation at a corner — written in terms of `angleAtCrossing`, which at
a corner unfolds to `arg L_+ - arg(-L_-)` for the canonical one-sided derivative
limits — bridge it to the unit-circle power equation
`(L_+/‖L_+‖)^k = ((-L_-)/‖L_-‖)^k`. This packages the angle data for use with
`cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric_corner`. -/
theorem corner_angle_compat_to_h_B
    (γ : ClosedPwC1Immersion x)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_part : t₀ ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition)
    {L_minus L_plus : ℂ} (hL_minus_ne : L_minus ≠ 0) (hL_plus_ne : L_plus ≠ 0)
    (hL_left_spec : L_minus = Classical.choose
      (γ.toPwC1Immersion.left_deriv_limit t₀ h_part))
    (hL_right_spec : L_plus = Classical.choose
      (γ.toPwC1Immersion.right_deriv_limit t₀ h_part))
    {k : ℕ} (hk : 2 ≤ k)
    (h_angle_raw : ∃ m : ℤ,
      ((k - 1 : ℕ) : ℝ) * angleAtCrossing γ.toPwC1Immersion t₀ ht₀ =
        (m : ℝ) * (2 * Real.pi)) :
    (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
    ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1) := by
  have h_angle_eq : angleAtCrossing γ.toPwC1Immersion t₀ ht₀ =
      Complex.arg L_plus - Complex.arg (-L_minus) := by
    unfold angleAtCrossing
    rw [dif_pos h_part]
    rw [← hL_left_spec, ← hL_right_spec]
  rw [h_angle_eq] at h_angle_raw
  exact h_B_of_angle_compat_corner hL_minus_ne hL_plus_ne hk h_angle_raw

/-- **HW3.3 — Truly full-spec form (T-BR-Y10b).**

The final paper-faithful spec of Hungerbühler–Wasem Theorem 3.3, with NO
technical residual hypotheses beyond the spec:

```
(hU_open, hU_ne, hS_in_U, hf, h_null, hMero, hCondB, hCondA, h_unique_cross)
```

Both smooth and corner crossings are admissible: the proof case-splits on
each unique crossing's partition status and dispatches to the appropriate
smooth/corner infrastructure. The `h_no_corner_crossings` hypothesis required
by `_no_basepoint_no_unique_constraint_of_unique` is now eliminated.

`h_unique_cross` (each pole crossed at most once) is the only remaining
parametric assumption beyond the paper spec. Eliminating it requires the
per-window aggregation for multi-crossing CPV, which is exposed as the
named oracle in `residueTheorem_crossing_no_basepoint_no_unique_constraint`.

`hx_notin_S` is auto-discharged: if `x ∈ S`, then `h_unique_cross s := x`
applied to `t₁ := 0, t₂ := 1` (where `γ 0 = γ 1 = x ∈ S`) yields `0 = 1`,
a contradiction. -/
theorem residueTheorem_crossing_truly_full_spec
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => (PolarPartDecomposition.ofMeromorphicWithCondB hU_open hS_in_U hf
        (γ := γ.toPwC1Immersion) hMero hCondB).order s))
    (h_unique_cross : ∀ s ∈ S, ∀ t₁ ∈ Set.Icc (0 : ℝ) 1,
      ∀ t₂ ∈ Set.Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t₁ = s →
        γ.toPwC1Immersion.toPiecewiseC1Path t₂ = s →
        t₁ = t₂) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set decomp : PolarPartDecomposition f S U :=
    PolarPartDecomposition.ofMeromorphicWithCondB hU_open hS_in_U hf
      (γ := γ.toPwC1Immersion) hMero hCondB
  have hx_notin_S : x ∉ (↑S : Set ℂ) := fun hx => zero_ne_one
    (h_unique_cross x hx 0 (Set.left_mem_Icc.mpr zero_le_one)
      1 (Set.right_mem_Icc.mpr zero_le_one)
      γ.toPwC1Immersion.toPiecewiseC1Path.apply_zero
      γ.toPwC1Immersion.toPiecewiseC1Path.apply_one)
  refine residueTheorem_crossing_compositional hU_open hU_ne S hS_in_U f hf γ
    h_null decomp ?_
  intro s hs
  by_cases h_avoid : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s
  · exact cpv_polarPart_at_uncrossed_pole hU_open hU_ne hS_in_U γ h_null decomp s hs
      h_avoid
  · push Not at h_avoid
    obtain ⟨t₀, ht₀_Icc, h_at_t₀⟩ := h_avoid
    have h0_ne : (γ.toPwC1Immersion : ℝ → ℂ) 0 ≠ s := by
      simp only [show (γ.toPwC1Immersion : ℝ → ℂ) 0 =
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 0 from rfl,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend_zero]
      exact fun h_eq => hx_notin_S (h_eq ▸ hs)
    have h1_ne : (γ.toPwC1Immersion : ℝ → ℂ) 1 ≠ s := by
      simp only [show (γ.toPwC1Immersion : ℝ → ℂ) 1 =
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 1 from rfl,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend_one]
      exact fun h_eq => hx_notin_S (h_eq ▸ hs)
    have ht₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht₀_Icc.1 fun h_eq => h0_ne (h_eq ▸ h_at_t₀),
       lt_of_le_of_ne ht₀_Icc.2 fun h_eq => h1_ne (h_eq.symm ▸ h_at_t₀)⟩
    have h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path t = s → t = t₀ :=
      fun t ht h_eq => h_unique_cross s hs t ht t₀ ht₀_Icc h_eq h_at_t₀
    obtain ⟨n, hn1, h_order_le_n, h_flat_n⟩ :=
      flat_data_of_condA_at_crossing decomp hCondA hs ht₀_Ioo h_at_t₀
    have h_flat_one : IsFlatOfOrder
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ 1 :=
      h_flat_n.of_le hn1 γ.toPwC1Immersion.continuous.continuousAt
    have h_cpv_exists := hasCauchyPV_inv_sub_of_flat_one_full γ ht₀_Ioo h_at_t₀
      h_unique h_flat_one
    let D : AsymmetricSingleCrossingData
        γ.toPwC1Immersion.toPiecewiseC1Path s :=
      HungerbuhlerWasem.AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV_anywhere
        γ ht₀_Ioo h_at_t₀ h_unique h_cpv_exists.choose_spec
    by_cases h_part : t₀ ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
    · set L_minus : ℂ :=
        Classical.choose (γ.toPwC1Immersion.left_deriv_limit t₀ h_part)
        with hL_minus_def
      set L_plus : ℂ :=
        Classical.choose (γ.toPwC1Immersion.right_deriv_limit t₀ h_part)
        with hL_plus_def
      have hL_minus_spec := Classical.choose_spec
        (γ.toPwC1Immersion.left_deriv_limit t₀ h_part)
      have hL_plus_spec := Classical.choose_spec
        (γ.toPwC1Immersion.right_deriv_limit t₀ h_part)
      have h_angle_anywhere :=
        angle_compat_of_condB_anywhere hU_open hS_in_U γ decomp hCondB hs ht₀_Ioo h_at_t₀
      have h_B : ∀ (k : Fin (decomp.order s)), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
          (L_plus / (↑‖L_plus‖ : ℂ)) ^ k.val =
          ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ k.val := fun k hk hne => by
        have h_result :=
          corner_angle_compat_to_h_B γ ht₀_Ioo h_part hL_minus_spec.1 hL_plus_spec.1
            hL_minus_def hL_plus_def (by omega : 2 ≤ k.val + 1)
            (by rw [show ((k.val + 1) - 1 : ℕ) = k.val from by omega]
                exact h_angle_anywhere k hk hne)
        rwa [show k.val + 1 - 1 = k.val from by omega] at h_result
      exact MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole
        hS_in_U decomp γ hs h_null
        (cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric_corner
          hS_in_U γ h_null decomp s hs ht₀_Ioo h_at_t₀ h_unique
          hL_minus_spec.1 hL_plus_spec.1 hL_plus_spec.2 hL_minus_spec.2 D n h_flat_n
          hn1 h_order_le_n h_B)
    · exact MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole
        hS_in_U decomp γ hs h_null
        (cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric
          hS_in_U γ h_null decomp s hs ht₀_Ioo h_at_t₀ h_unique h_part D n h_flat_n
          hn1 h_order_le_n
          (angle_compat_of_condB hU_open hS_in_U γ decomp hCondB hs ht₀_Ioo h_at_t₀ h_part))

end HungerbuhlerWasem

end
