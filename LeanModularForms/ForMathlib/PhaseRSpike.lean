/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HW33Clean
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ForMathlib.FDBoundaryReparametrization
import LeanModularForms.ForMathlib.ValenceFormula.WindingWeights.I
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.ArcCalculus
import LeanModularForms.SpherePacking.RectangularContour

/-!
# Phase-R feasibility spike: the pentagon via HW 3.3

**Question** (CONSOLIDATION_PLAN.md §4 row S): can the valence formula's bespoke
pentagon PV machinery be replaced by instantiating HW 3.3?

**Test instance**: `f z = (z − i)⁻¹`, `S = {i}` (simple pole that the pentagon
crosses on its circular arc, at parameter `t = 2/5`), `U` = open upper half-plane.

**What this file proves** (no sorries in the compositional route):

* `pentagonContour` — the fundamental-domain boundary `fdBoundaryFun H` on `[0,1]`
  as a `ClosedPwC1Immersion (fdStart H)` (the HW 3.3 curve class), built on top of
  the existing `fdBoundaryPC1Path` with the closed-piece data supplied by
  `affineSegment` (three straight pieces) and `ArcCalculus.unitArc` (the arc).
* `pentagon_hasCauchyPVOn_via_hw33` — the HW residue engine applied to the
  pentagon: CPV of `(z−i)⁻¹` along the pentagon exists and equals
  `2πi · w(γ, i)`, via `residueTheorem_crossing_compositional` +
  `cpv_polarPart_at_multiCrossed_pole_under_condB_corner` +
  `hasCauchyPV_inv_sub_multiCrossing_corner` (generic CPV existence at crossed
  poles!) + `IsNullHomologous.of_convex_open`. **No crossing-set identification,
  no angle computation, no FTC telescope** — all of that is generic.
* `pentagon_gWN_at_I` — the winding value `w(γ, i) = −1/2`, extracted by playing
  the HW conclusion against the protected `pv_integral_at_i_tendsto` (the value
  anchor comes from the classical computation; HW supplies existence + shape).
* `pv_integral_at_i_tendsto_via_hw33` — the protected trio statement at `i`
  recovered **verbatim** as a corollary of the HW route (given the anchor).

**Key negative finding** (`pentagon_via_hw33_clean_route`): the protected crown
`hw_3_3_clean_full_mero` is NOT directly instantiable on the pentagon, because
its `hCondA` hypothesis demands flatness of order
`(PolarPartDecomposition.ofMeromorphicWithCondB …).order s`, which unfolds to
`meroPolarOrderAt = (mero_laurent_data_exists hMero).choose` — a
`Classical.choose`-opaque `N`. On the *curved* arc, `IsFlatOfOrder` holds only
for `n = 1`, and `N = 1` is not provable (the existential admits any `N ≥ 1`
with vanishing higher coefficients). The compositional layer
(`residueTheorem_crossing_compositional`), which takes a *caller-supplied*
`PolarPartDecomposition` (here with `order ≡ 1` by construction), is the correct
entry point — or `mero_laurent_data_exists` should be fixed upstream to return
the canonical minimal `N`.

This file is a SPIKE: it is deliberately not added to the root
`LeanModularForms.lean` index, and the clean-route section carries annotated
sorries. See `.mathlib-quality/phase-r-spike-memo.md` for the verdict.
-/

open Complex Set Filter Topology MeasureTheory HungerbuhlerWasem
open scoped Real Interval

noncomputable section

namespace LeanModularForms

namespace PhaseRSpike

/-! ## §1 The pentagon's pieces: three affine segments and one circular arc

`fdBoundaryFun H` on `[0,1]` is, piece by piece:
* `[0, 1/5]`: the right vertical edge `fdStart H = 1/2 + Hi → ρ+1`,
* `[1/5, 3/5]`: ONE analytic circular arc `e^{iθ(t)}`, `θ(t) = (5t+1)π/6`,
  from `ρ+1` through `i` (at `t = 2/5`) to `ρ` — the inherited partition splits
  it at `2/5`, but both halves are literally the same function,
* `[3/5, 4/5]`: the left vertical edge `ρ → −1/2 + Hi`,
* `[4/5, 1]`: the top edge `−1/2 + Hi → 1/2 + Hi`. -/

/-- The arc piece: `exp(iθ(t))` with `θ(t) = π/3 + ((t−1/5)/(2/5))·(π/3)`,
covering both arc sub-pieces of the inherited partition. -/
private def pentArc : ℝ → ℂ :=
  ArcCalculus.unitArc (Real.pi / 3) (2 * Real.pi / 3) (1/5) (3/5)

private lemma pentArc_hasDerivAt (t : ℝ) :
    HasDerivAt pentArc
      (pentArc t * (↑((2 * Real.pi / 3 - Real.pi / 3) / ((3:ℝ)/5 - 1/5)) * I)) t :=
  ArcCalculus.unitArc_hasDerivAt _ _ _ _ t (by norm_num)

private lemma pentArc_ne_zero (t : ℝ) : pentArc t ≠ 0 :=
  Complex.exp_ne_zero _

private lemma pentArc_contDiff : ContDiff ℝ 1 pentArc := by
  unfold pentArc ArcCalculus.unitArc
  have h_inner : ContDiff ℝ 1 (fun t : ℝ =>
      (↑(Real.pi / 3 + (t - 1/5) / ((3:ℝ)/5 - 1/5) * (2 * Real.pi / 3 - Real.pi / 3)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp <| contDiff_const.add
      (((contDiff_id.sub contDiff_const).div_const _).mul contDiff_const)
  exact Complex.contDiff_exp.comp (h_inner.mul contDiff_const)

/-- The pentagon's right vertical edge as an `affineSegment`. -/
private lemma eqOn_seg1 (H : ℝ) :
    EqOn (fdBoundaryFun H)
      (affineSegment 5 0 (fdStart H) ((1:ℂ)/2 + ↑(Real.sqrt 3)/2 * I))
      (Icc 0 (1/5 : ℝ)) := fun t ht => by
  simp only [fdBoundaryFun, if_pos ht.2, affineSegment, fdStart, Complex.real_smul]
  push_cast
  ring

/-- The pentagon's arc piece: `fdBoundaryFun` agrees with `pentArc` on `[1/5, 3/5]`.
Both arc branches of `fdBoundaryFun` are restrictions of the same analytic arc. -/
private lemma eqOn_arc (H : ℝ) :
    EqOn (fdBoundaryFun H) pentArc (Icc (1/5 : ℝ) (3/5)) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with heq | h1
  · -- t = 1/5: junction value ρ+1 = e^{iπ/3} on both sides
    subst heq
    simp only [fdBoundaryFun, if_pos (le_refl (1/5 : ℝ)), pentArc, ArcCalculus.unitArc]
    rw [show (Real.pi / 3 + ((1:ℝ)/5 - 1/5) / ((3:ℝ)/5 - 1/5) * (2 * Real.pi / 3 - Real.pi / 3))
        = Real.pi / 3 by ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast
    ring
  rcases le_or_gt t (2/5) with h2 | h2
  · -- (1/5, 2/5]: branch 2 of fdBoundaryFun
    simp only [fdBoundaryFun, if_neg (not_le.mpr h1), if_pos h2, pentArc, ArcCalculus.unitArc]
    congr 1
    push_cast
    ring
  · -- (2/5, 3/5]: branch 3 of fdBoundaryFun
    have hn1 : ¬ t ≤ 1/5 := not_le.mpr h1
    have hn2 : ¬ t ≤ 2/5 := not_le.mpr h2
    simp only [fdBoundaryFun, if_neg hn1, if_neg hn2, if_pos ht.2, pentArc,
      ArcCalculus.unitArc]
    congr 1
    push_cast
    ring

/-- The pentagon's left vertical edge as an `affineSegment`. -/
private lemma eqOn_seg4 (H : ℝ) :
    EqOn (fdBoundaryFun H)
      (affineSegment 5 3 (-(1:ℂ)/2 + ↑(Real.sqrt 3)/2 * I) (-(1:ℂ)/2 + ↑H * I))
      (Icc (3/5 : ℝ) (4/5)) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with heq | h3
  · -- t = 3/5: junction value ρ = e^{2πi/3} on the arc side
    subst heq
    have hn1 : ¬ (3/5 : ℝ) ≤ 1/5 := by norm_num
    have hn2 : ¬ (3/5 : ℝ) ≤ 2/5 := by norm_num
    simp only [fdBoundaryFun, if_neg hn1, if_neg hn2, if_pos (le_refl (3/5 : ℝ)),
      affineSegment, Complex.real_smul]
    rw [show ((↑Real.pi / 2 + (5 * (↑(3/5 : ℝ) : ℂ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)
        = ↑(2 * Real.pi / 3) * I by push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast
    ring
  · -- (3/5, 4/5]: branch 4
    have hn1 : ¬ t ≤ 1/5 := by intro h; linarith
    have hn2 : ¬ t ≤ 2/5 := by intro h; linarith
    have hn3 : ¬ t ≤ 3/5 := not_le.mpr h3
    simp only [fdBoundaryFun, if_neg hn1, if_neg hn2, if_neg hn3, if_pos ht.2,
      affineSegment, Complex.real_smul]
    push_cast
    ring

/-- The pentagon's top edge as an `affineSegment`. -/
private lemma eqOn_seg5 (H : ℝ) :
    EqOn (fdBoundaryFun H)
      (affineSegment 5 4 (-(1:ℂ)/2 + ↑H * I) ((1:ℂ)/2 + ↑H * I))
      (Icc (4/5 : ℝ) 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with heq | h4
  · -- t = 4/5: junction value −1/2 + Hi on the seg4 side
    subst heq
    have hn1 : ¬ (4/5 : ℝ) ≤ 1/5 := by norm_num
    have hn2 : ¬ (4/5 : ℝ) ≤ 2/5 := by norm_num
    have hn3 : ¬ (4/5 : ℝ) ≤ 3/5 := by norm_num
    simp only [fdBoundaryFun, if_neg hn1, if_neg hn2, if_neg hn3,
      if_pos (le_refl (4/5 : ℝ)), affineSegment, Complex.real_smul]
    push_cast
    ring
  · -- (4/5, 1]: branch 5
    have hn1 : ¬ t ≤ 1/5 := by intro h; linarith
    have hn2 : ¬ t ≤ 2/5 := by intro h; linarith
    have hn3 : ¬ t ≤ 3/5 := by intro h; linarith
    have hn4 : ¬ t ≤ 4/5 := not_le.mpr h4
    simp only [fdBoundaryFun, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4,
      affineSegment, Complex.real_smul]
    push_cast
    ring

/-! ## §2 Lifting the piece descriptions to the bundled path -/

private lemma pentExtend_eq (H : ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (fdBoundaryPath H).extend t = fdBoundaryFun H t :=
  Path.extend_apply _ ht

private lemma extend_eqOn {H : ℝ} {g : ℝ → ℂ} {a b : ℝ}
    (hsub : Icc a b ⊆ Icc (0:ℝ) 1) (h : EqOn (fdBoundaryFun H) g (Icc a b)) :
    EqOn (fdBoundaryPath H).extend g (Icc a b) := fun _t ht =>
  (pentExtend_eq H (hsub ht)).trans (h ht)

/-! ## §3 The pentagon as a `ClosedPwC1Immersion` -/

/-- Closed partition of the pentagon: endpoints adjoined to `fdBoundaryPartition`. -/
private def pentClosedPartition : Finset ℝ := {0, 1/5, 2/5, 3/5, 4/5, 1}

private lemma pentClosedPartition_eq :
    pentClosedPartition = insert 0 (insert 1 fdBoundaryPartition) := by
  ext x
  simp only [pentClosedPartition, fdBoundaryPartition, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

private lemma pentClosedPartition_subset_Icc :
    (pentClosedPartition : Set ℝ) ⊆ Icc 0 1 := by
  intro x hx
  simp only [pentClosedPartition, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
    mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma pentClosedPartition_consecutive_cases {p q : ℝ}
    (h : pentClosedPartition.IsConsecutive p q) :
    (p = 0 ∧ q = 1/5) ∨ (p = 1/5 ∧ q = 2/5) ∨ (p = 2/5 ∧ q = 3/5) ∨
      (p = 3/5 ∧ q = 4/5) ∨ (p = 4/5 ∧ q = 1) := by
  obtain ⟨hp, hq, hpq, hno⟩ := h
  have h1 := hno (1/5) (by norm_num [pentClosedPartition])
  have h2 := hno (2/5) (by norm_num [pentClosedPartition])
  have h3 := hno (3/5) (by norm_num [pentClosedPartition])
  have h4 := hno (4/5) (by norm_num [pentClosedPartition])
  simp only [pentClosedPartition, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (revert hpq h1 h2 h3 h4; norm_num [mem_Ioo])

/-- **The pentagon (fundamental-domain boundary at height `H`) as a
`ClosedPwC1Immersion`** — the curve class of HW 3.3. Reuses the existing
`fdBoundaryPC1Path` and supplies the closed-piece `C¹`/non-vanishing data. -/
def pentagonContour (H : ℝ) (hH : H > Real.sqrt 3 / 2) :
    ClosedPwC1Immersion (fdStart H) where
  toPiecewiseC1Path := fdBoundaryPC1Path H hH
  closedPartition := pentClosedPartition
  zero_mem_closedPartition := by simp [pentClosedPartition]
  one_mem_closedPartition := by simp [pentClosedPartition]
  closedPartition_subset := pentClosedPartition_subset_Icc
  closedPartition_eq := pentClosedPartition_eq
  contDiffOn_pieces := by
    intro p q hcons
    show ContDiffOn ℝ 1 (fdBoundaryPath H).extend (Icc p q)
    rcases pentClosedPartition_consecutive_cases hcons with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact affineSegment_contDiffOn_of_eqOn
        (extend_eqOn (Icc_subset_Icc le_rfl (by norm_num)) (eqOn_seg1 H))
    · exact pentArc_contDiff.contDiffOn.congr
        ((extend_eqOn (Icc_subset_Icc (by norm_num) (by norm_num)) (eqOn_arc H)).mono
          (Icc_subset_Icc le_rfl (by norm_num)))
    · exact pentArc_contDiff.contDiffOn.congr
        ((extend_eqOn (Icc_subset_Icc (by norm_num) (by norm_num)) (eqOn_arc H)).mono
          (Icc_subset_Icc (by norm_num) le_rfl))
    · exact affineSegment_contDiffOn_of_eqOn
        (extend_eqOn (Icc_subset_Icc (by norm_num) (by norm_num)) (eqOn_seg4 H))
    · exact affineSegment_contDiffOn_of_eqOn
        (extend_eqOn (Icc_subset_Icc (by norm_num) le_rfl) (eqOn_seg5 H))
  derivWithin_ne_zero_pieces := by
    intro p q hcons t ht
    show derivWithin (fdBoundaryPath H).extend (Icc p q) t ≠ 0
    have harc_ne : ∀ {a b : ℝ}, a < b →
        EqOn (fdBoundaryPath H).extend pentArc (Icc a b) → t ∈ Icc a b →
        derivWithin (fdBoundaryPath H).extend (Icc a b) t ≠ 0 := by
      intro a b hab heq ht'
      rw [((pentArc_hasDerivAt t).hasDerivWithinAt.congr_of_eventuallyEq
        (Filter.eventually_of_mem self_mem_nhdsWithin heq) (heq ht')).derivWithin
        (uniqueDiffOn_Icc hab t ht')]
      refine mul_ne_zero (pentArc_ne_zero t) (mul_ne_zero ?_ Complex.I_ne_zero)
      rw [show ((2 * Real.pi / 3 - Real.pi / 3) / ((3:ℝ)/5 - 1/5)) = 5 * Real.pi / 6 by ring]
      exact_mod_cast Complex.ofReal_ne_zero.mpr (by positivity)
    rcases pentClosedPartition_consecutive_cases hcons with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [affineSegment_derivWithin_of_eqOn
        (extend_eqOn (Icc_subset_Icc le_rfl (by norm_num)) (eqOn_seg1 H)) (by norm_num) ht]
      refine smul_ne_zero (by norm_num) ?_
      rw [show ((1:ℂ)/2 + ↑(Real.sqrt 3)/2 * I) - fdStart H
          = ↑(Real.sqrt 3 / 2 - H) * I by simp only [fdStart]; push_cast; ring]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)) Complex.I_ne_zero
    · exact harc_ne (by norm_num)
        ((extend_eqOn (Icc_subset_Icc (by norm_num) (by norm_num)) (eqOn_arc H)).mono
          (Icc_subset_Icc le_rfl (by norm_num))) ht
    · exact harc_ne (by norm_num)
        ((extend_eqOn (Icc_subset_Icc (by norm_num) (by norm_num)) (eqOn_arc H)).mono
          (Icc_subset_Icc (by norm_num) le_rfl)) ht
    · rw [affineSegment_derivWithin_of_eqOn
        (extend_eqOn (Icc_subset_Icc (by norm_num) (by norm_num)) (eqOn_seg4 H))
        (by norm_num) ht]
      refine smul_ne_zero (by norm_num) ?_
      rw [show (-(1:ℂ)/2 + ↑H * I) - (-(1:ℂ)/2 + ↑(Real.sqrt 3)/2 * I)
          = ↑(H - Real.sqrt 3 / 2) * I by push_cast; ring]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)) Complex.I_ne_zero
    · rw [affineSegment_derivWithin_of_eqOn
        (extend_eqOn (Icc_subset_Icc (by norm_num) le_rfl) (eqOn_seg5 H)) (by norm_num) ht]
      refine smul_ne_zero (by norm_num) ?_
      rw [show ((1:ℂ)/2 + ↑H * I) - (-(1:ℂ)/2 + ↑H * I) = 1 by ring]
      exact one_ne_zero

/-! ## §4 Null-homology in the upper half-plane (framework reuse) -/

/-- The ambient domain: the open upper half-plane. -/
private def UHP : Set ℂ := {z : ℂ | 0 < z.im}

private lemma UHP_open : IsOpen UHP := isOpen_lt continuous_const Complex.continuous_im

private lemma UHP_ne : UHP.Nonempty := ⟨I, by simp [UHP]⟩

private lemma UHP_convex : Convex ℝ UHP := convex_halfSpace_im_gt 0

private lemma S_subset_UHP : (↑({I} : Finset ℂ) : Set ℂ) ⊆ UHP := by
  simp [UHP]

/-- The pentagon's image lies in the upper half-plane (via the `[0,5]`-chain
bound `fdBoundary_H_im_pos` and the in-tree reparametrisation). -/
private lemma pentagon_image_subset (H : ℝ) (hH : H > Real.sqrt 3 / 2) :
    ∀ t ∈ Icc (0:ℝ) 1,
      (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path t ∈ UHP := by
  intro t ht
  show 0 < ((fdBoundaryPath H).extend t).im
  rw [pentExtend_eq H ht, fdBoundaryFun_eq_fdBoundary_H_scaled]
  exact fdBoundary_H_im_pos H hH (5 * t) ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Null-homology of the pentagon in the upper half-plane — direct reuse of the
campaign-batch-1 framework lemma `IsNullHomologous.of_convex_open`. -/
private lemma pentagon_null_homologous (H : ℝ) (hH : H > Real.sqrt 3 / 2) :
    IsNullHomologous (pentagonContour H hH).toPwC1Immersion UHP :=
  IsNullHomologous.of_convex_open _ UHP_open UHP_convex (pentagon_image_subset H hH)

/-! ## §5 The test function and its by-hand polar-part decomposition -/

private lemma hf_test : DifferentiableOn ℂ (fun z : ℂ => (z - I)⁻¹)
    (UHP \ (↑({I} : Finset ℂ) : Set ℂ)) := fun z hz =>
  (((differentiableAt_id.sub (differentiableAt_const I)).inv
    (sub_ne_zero.mpr (by simpa using hz.2))).differentiableWithinAt)

private lemma hMero_test : ∀ s ∈ ({I} : Finset ℂ),
    MeromorphicAt (fun z : ℂ => (z - I)⁻¹) s := fun _s _ =>
  ((analyticAt_id.sub analyticAt_const).meromorphicAt).inv

private lemma fdStart_ne_I (H : ℝ) : fdStart H ∉ (↑({I} : Finset ℂ) : Set ℂ) := by
  simp only [Finset.coe_singleton, mem_singleton_iff, fdStart]
  intro h
  have := congrArg Complex.re h
  simp at this

private lemma residue_inv_sub_I : residue (fun z : ℂ => (z - I)⁻¹) I = 1 := by
  have h := residue_of_laurent_expansion (f := fun z : ℂ => (z - I)⁻¹) (s := I)
    1 (fun _ => 1) (g := fun _ => 0) analyticAt_const
    (by filter_upwards with z; simp [one_div])
  rw [h, dif_pos one_pos]

/-- A by-hand `PolarPartDecomposition` for `(z−i)⁻¹` with `order ≡ 1` BY
CONSTRUCTION. This sidesteps the `Classical.choose`-opaque order of
`PolarPartDecomposition.ofMeromorphicWithCondB` (see the SPIKE-GAP in §8):
with a definitional order, the condition-A′ obligation is flatness of order 1,
which `isFlatOfOrder_one` discharges for every pw-C¹ immersion. -/
private def spikeDecomp : PolarPartDecomposition (fun z : ℂ => (z - I)⁻¹) {I} UHP where
  polarPart := fun s z => (z - s)⁻¹
  order := fun _ => 1
  coeff := fun _ _ => 1
  polarPart_eq := by
    intro s _ z _
    simp [one_div]
  residue_eq := by
    intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    rw [residue_inv_sub_I, dif_pos one_pos]
  analyticRemainder := fun _ => 0
  analyticRemainder_diff := differentiableOn_const 0
  decomp := by
    intro z _
    simp

/-! ## §6 The HW 3.3 instantiation (compositional route, sorry-free) -/

/-- **The spike headline.** HW 3.3 applied to the pentagon crossing the simple
pole at `i`: the multi-point CPV of `(z−i)⁻¹` along `fdBoundaryFun H` exists and
equals `2πi · w(γ, i)`. Everything is discharged by generic HW machinery:

* CPV existence at the crossed pole: `hasCauchyPV_inv_sub_multiCrossing_corner`
  (needs only the abstract crossing set from `crossings_finset_of_endpts_off`
  and order-1 flatness from `isFlatOfOrder_one`);
* per-pole polar CPV: `cpv_polarPart_at_multiCrossed_pole_under_condB_corner`
  (its corner-form condition (B) is **vacuous** for a simple pole);
* assembly: `residueTheorem_crossing_compositional`;
* topology: `IsNullHomologous.of_convex_open`.

No crossing-parameter identification (`γ t = i ↔ t = 2/5`), no tangent/angle
computation, and no bespoke FTC telescope is required. -/
theorem pentagon_hasCauchyPVOn_via_hw33 (H : ℝ) (hH : H > Real.sqrt 3 / 2) :
    HasCauchyPVOn {I} (fun z : ℂ => (z - I)⁻¹)
      (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I *
        generalizedWindingNumber
          (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path I) := by
  classical
  obtain ⟨crossings, h_Ioo, h_at, h_complete⟩ :=
    crossings_finset_of_endpts_off (pentagonContour H hH)
      (Finset.mem_singleton_self I) (fdStart_ne_I H)
  have h_flat : ∀ t₀ ∈ crossings,
      IsFlatOfOrder
        (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ 1 :=
    fun t₀ ht₀ => isFlatOfOrder_one (pentagonContour H hH).toPwC1Immersion t₀ (h_Ioo t₀ ht₀)
  obtain ⟨L_plus, L_minus, _, _, hLp_ne, hLm_ne, hLp, hLm⟩ :=
    canonical_derivLimits_at_crossings_exists (pentagonContour H hH) h_Ioo
  have h_simple : ∃ L : ℂ, HasCauchyPV (fun z => (z - I)⁻¹)
      (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path I L :=
    hasCauchyPV_inv_sub_multiCrossing_corner h_Ioo h_at h_complete h_flat
  have h_polar : ∀ s ∈ ({I} : Finset ℂ),
      HasCauchyPVOn {I} (spikeDecomp.polarPart s)
        (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path
        (2 * ↑Real.pi * I *
          generalizedWindingNumber
            (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path s *
          residue (fun z : ℂ => (z - I)⁻¹) s) := by
    intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    exact cpv_polarPart_at_multiCrossed_pole_under_condB_corner
      (Finset.mem_singleton_self I) spikeDecomp h_Ioo h_at h_complete
      h_flat L_plus L_minus hLp_ne hLm_ne hLp hLm
      (fun k hk1 _ _ _ => absurd (show k.val < 1 from k.isLt) (by omega))
      h_simple
  have h_final := residueTheorem_crossing_compositional UHP_open UHP_ne
    {I} S_subset_UHP _ hf_test (pentagonContour H hH)
    (pentagon_null_homologous H hH) spikeDecomp h_polar
  rwa [Finset.sum_singleton, residue_inv_sub_I, mul_one] at h_final

/-! ## §7 The bridge to the protected `[0,5]` statement and the value anchor -/

/-- `√3/2 < 1` (so `1 < H` implies the contour hypothesis `√3/2 < H`). -/
private lemma sqrt3_div_two_lt_one : Real.sqrt 3 / 2 < 1 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]

/-- The protected `pv_integral_at_i_tendsto`, transported through the in-tree
`[0,5] → [0,1]` reparametrisation bridge into `HasCauchyPVOn` form. -/
private lemma pentagon_hasCauchyPVOn_classical (H : ℝ) (hH1 : 1 < H)
    (hH : H > Real.sqrt 3 / 2) :
    HasCauchyPVOn {I} (fun z : ℂ => (z - I)⁻¹)
      (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path
      (-(I * ↑Real.pi)) := by
  refine hasCauchyPVOn_of_cauchyPVOn'_tendsto _ (fun t ht => pentExtend_eq H ht) ?_
  refine (pv_integral_at_i_tendsto H hH1).congr fun ε => ?_
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Finset.mem_singleton, exists_eq_left, deriv_sub_const]
  by_cases hc : ‖fdBoundary_H H t - I‖ ≤ ε
  · rw [if_neg (not_lt.mpr hc), if_pos hc]
  · rw [if_pos (lt_of_not_ge hc), if_neg hc]

/-- **The winding-value anchor**: the pentagon's generalized winding number at
`i` is `−1/2`, by uniqueness of limits between the HW-route CPV
(`pentagon_hasCauchyPVOn_via_hw33`) and the protected classical computation.

NOTE the division of labour this makes explicit: HW 3.3 delivers CPV
*existence* and the residue-sum *shape* generically; the protected
`pv_integral_at_*` trio is precisely the per-point numeric anchor `w = −1/2`
(resp. `−1/6` at the corners) which no generic theorem can supply. -/
theorem pentagon_gWN_at_I (H : ℝ) (hH1 : 1 < H) (hH : H > Real.sqrt 3 / 2) :
    generalizedWindingNumber
      (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path I = -(1/2 : ℂ) := by
  have h_eq : 2 * ↑Real.pi * I *
      generalizedWindingNumber
        (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path I
      = -(I * ↑Real.pi) :=
    tendsto_nhds_unique (pentagon_hasCauchyPVOn_via_hw33 H hH)
      (pentagon_hasCauchyPVOn_classical H hH1 hH)
  refine mul_left_cancel₀ Complex.two_pi_I_ne_zero (h_eq.trans ?_)
  ring

/-- Reverse direction of the (private) extend-congruence in
`FDBoundaryReparametrization`: replace `extend` by `fdBoundaryFun` under the
multi-point CPV integral. -/
private lemma integral_cpvIntegrandOn_pentagon_extend_eq {H : ℝ}
    (hH : H > Real.sqrt 3 / 2) (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) :
    (∫ t in (0:ℝ)..1, cpvIntegrandOn S f
      ((pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path.toPath.extend) ε t) =
    ∫ t in (0:ℝ)..1, cpvIntegrandOn S f (fdBoundaryFun H) ε t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (1:ℝ))] with t ht1 htm
  rw [uIoc_of_le (zero_le_one' ℝ)] at htm
  have ht : t ∈ Ioo (0:ℝ) 1 := ⟨htm.1, lt_of_le_of_ne htm.2 (by simpa using ht1)⟩
  have hev : (fdBoundaryPath H).extend =ᶠ[𝓝 t] fdBoundaryFun H := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact pentExtend_eq H (Ioo_subset_Icc_self hu)
  show cpvIntegrandOn S f (fdBoundaryPath H).extend ε t = _
  simp only [cpvIntegrandOn, pentExtend_eq H (Ioo_subset_Icc_self ht), hev.deriv_eq]

/-- **The protected statement at `i`, recovered verbatim from the HW route.**
The statement is byte-identical to `pv_integral_at_i_tendsto`. The proof runs:
HW compositional CPV (existence + shape, §6) + winding anchor (§7) + the
reparametrisation bridge run in reverse. -/
theorem pv_integral_at_i_tendsto_via_hw33 (H : ℝ) (hH : 1 < H) :
    Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - I‖ > ε
      then (fdBoundary_H H t - I)⁻¹ *
           deriv (fun s => fdBoundary_H H s - I) t
      else 0) (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi))) := by
  have hH' : H > Real.sqrt 3 / 2 := lt_trans sqrt3_div_two_lt_one hH
  have h_hw := pentagon_hasCauchyPVOn_via_hw33 H hH'
  rw [pentagon_gWN_at_I H hH hH',
    show (2 * ↑Real.pi * I * -(1/2 : ℂ)) = -(I * ↑Real.pi) by ring] at h_hw
  refine h_hw.congr fun ε => ?_
  rw [integral_cpvIntegrandOn_pentagon_extend_eq hH' {I} _ ε,
    ← integral_cpvIntegrandOn_fdBoundary_H_eq_fdBoundaryFun {I} _ ε H]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Finset.mem_singleton, exists_eq_left, deriv_sub_const]
  by_cases hc : ‖fdBoundary_H H t - I‖ ≤ ε
  · rw [if_pos hc, if_neg (not_lt.mpr hc)]
  · rw [if_neg hc, if_pos (lt_of_not_ge hc)]

/-! ## §8 The clean-wrapper route (the protected crown) — partially blocked

`hw_3_3_clean_full_mero` bakes the choice-based
`PolarPartDecomposition.ofMeromorphicWithCondB` into the type of its `hCondA`
hypothesis. Its `.order s` is `meroPolarOrderAt = Classical.choose
(mero_laurent_data_exists hMero)` — an OPAQUE natural number: the existential
is satisfied by every `N ≥ 1` (pad with zero coefficients), so `order = 1` is
not provable. Since the pentagon crosses `i` on the *curved* arc,
`IsFlatOfOrder γ (2/5) n` is false for every `n ≥ 2` (the deviation from the
tangent is `Θ(dist²)`), so `hCondA` is genuinely undischargeable as stated.

This does not block Phase R — the compositional route (§6) is the right entry
point — but it means the *crown statement itself* cannot be the pentagon's
engine without an upstream fix to `mero_laurent_data_exists` (return the
canonical minimal `N`, e.g. via `meromorphicOrderAt`); the crown's statement
text would not change. -/

/-- Clean-wrapper instantiation, exhibiting which hypotheses are cheap (all
but two are discharged) and exactly where the wrapper is blocked. -/
theorem pentagon_via_hw33_clean_route (H : ℝ) (hH : H > Real.sqrt 3 / 2) :
    HasCauchyPVOn {I} (fun z : ℂ => (z - I)⁻¹)
      (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ ({I} : Finset ℂ), 2 * ↑Real.pi * I *
        generalizedWindingNumber
          (pentagonContour H hH).toPwC1Immersion.toPiecewiseC1Path s *
        residue (fun z : ℂ => (z - I)⁻¹) s) := by
  refine hw_3_3_clean_full_mero UHP_open UHP_ne S_subset_UHP hf_test
    (pentagonContour H hH) (pentagon_null_homologous H hH) hMero_test
    ⟨?_, ?_⟩ ?_ (fdStart_ne_I H)
  · -- SatisfiesConditionB.angle_rational
    -- SPIKE-GAP: angle rationality at the crossing t = 2/5. The inherited
    -- partition makes 2/5 a partition point, so `angleAtCrossing` takes the
    -- corner branch: `arg L₊ − arg(−L₋)` with `L₊ = L₋ = −5π/6` (both arc
    -- halves have the same tangent at i), giving angle = π = 1·π/1. Needs:
    -- crossing-set identification (γ t = i → t = 2/5; per-segment exclusion,
    -- ~70 lines, ingredients: Boundary/Bounds re/im lemmas + sin/cos injectivity
    -- as in OnCurvePV/Main.lean's h_arc_I_iff), one-sided deriv-limit pinning of
    -- the `Classical.choose` in `angleAtCrossing` via `tendsto_nhds_unique`
    -- against `pentArc_hasDerivAt`-based limits (~50 lines), and
    -- `Complex.arg_neg_ofReal`-style arithmetic (~15 lines).
    -- CHEAPER ALTERNATIVE (~25 lines): rebundle the pentagon with the coarser
    -- partition {1/5, 3/5, 4/5} (the arc is ONE analytic piece, eqOn_arc above);
    -- then 2/5 ∉ partition and `angleAtCrossing_smooth` gives angle = π directly.
    -- est. 135 lines as-is / 25 lines with coarse partition — NOT done in the
    -- spike because the compositional route (§6) never needs the angle.
    sorry
  · -- SatisfiesConditionB.laurent_compatible — fully discharged: for the simple
    -- pole the Laurent tail is empty and the `k ≥ 1` compatibility is vacuous.
    intro s hs t₀ _ _ _
    rw [Finset.mem_singleton] at hs
    subst hs
    exact ⟨1, fun _ => 1, fun _ => 0, analyticAt_const,
      by filter_upwards with z; simp [one_div],
      fun k _ hk => absurd hk (by have := k.isLt; omega)⟩
  · -- SatisfiesConditionA' w.r.t. the choice-based order
    -- SPIKE-GAP: UNDISCHARGEABLE AS STATED. The required flatness order is
    -- `(PolarPartDecomposition.ofMeromorphicWithCondB …).order I =
    -- (mero_laurent_data_exists hMero).choose` — Classical.choose-opaque.
    -- `IsFlatOfOrder` at order 1 holds (`isFlatOfOrder_one`), at order ≥ 2 it is
    -- FALSE on the curved arc, and the chosen N is provably neither.
    -- Fix lives upstream: make `mero_laurent_data_exists` return the canonical
    -- minimal N (via `meromorphicOrderAt`/`MeromorphicAt.order`), so that
    -- `meroPolarOrderAt hMero = 1` becomes a lemma for simple poles —
    -- est. 60–120 lines in HungerbuhlerWasem/LaurentExtraction.lean, no change
    -- to any protected statement's text. Until then, callers must use
    -- `residueTheorem_crossing_compositional` with a by-hand decomposition (§5–6).
    sorry

end PhaseRSpike

end LeanModularForms

end
