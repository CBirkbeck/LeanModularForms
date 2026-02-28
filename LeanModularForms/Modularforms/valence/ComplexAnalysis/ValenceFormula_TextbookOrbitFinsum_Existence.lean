/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_TextbookPackaging
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_OrbitSum
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_OrbitPairing

/-!
# Canonical Representatives for Non-Elliptic Orbits

This file proves that every non-elliptic orbit with nonzero order of vanishing
has a representative in the canonical finsets used by `valenceFormula_orbit_sum_S0`.

## Main Results

* `exists_repCanon_of_nonEllOrbit` — For any non-elliptic orbit `q` with `ordOrbit f q ≠ 0`,
  there exists `p ∈ RepCanon f hf` with `orb p = q`.
* `support_ordOrbit_nonEll_subset` — The support of the non-elliptic orbit summand
  is contained in the image of `RepCanon` under `orb`.

## Definitions

* `RepStrict` — interior representatives (‖p‖ > 1, |re| < 1/2, not elliptic)
* `RepLeftVert` — left vertical edge representatives (re = -1/2, ‖p‖ > 1)
* `RepLeftArc` — left arc representatives (‖p‖ = 1, re < 0, not ρ)
* `RepCanon` — union of the above three
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ## Canonical Representative Finsets -/

/-- Strict interior representatives: points in S0 with ‖p‖ > 1, |re| < 1/2, not elliptic.
Matches the first sum in `valenceFormula_orbit_sum_S0`. -/
noncomputable def RepStrict : Finset ℍ :=
  (S0 f hf).filter (fun p => p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧
    p ≠ ellipticPoint_rho_plus_one' ∧ ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)

/-- Left vertical edge representatives: points in S0 with re = -1/2, ‖p‖ > 1.
Matches the second sum in `valenceFormula_orbit_sum_S0`. -/
noncomputable def RepLeftVert : Finset ℍ := S_leftVert (S0 f hf)

/-- Left arc representatives: points in S0 with ‖p‖ = 1, re < 0, not ρ.
Matches the third sum in `valenceFormula_orbit_sum_S0`. -/
noncomputable def RepLeftArc : Finset ℍ :=
  (S0 f hf).filter (fun p => p ≠ ellipticPoint_rho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)

/-- The canonical representative finset: union of strict interior, left vertical, and left arc. -/
noncomputable def RepCanon : Finset ℍ :=
  RepStrict f hf ∪ RepLeftVert f hf ∪ RepLeftArc f hf

/-! ## Membership Lemmas -/

lemma repStrict_mem_S0 {p : ℍ} (hp : p ∈ RepStrict f hf) : p ∈ S0 f hf :=
  (Finset.mem_filter.mp hp).1

lemma repLeftVert_mem_S0 {p : ℍ} (hp : p ∈ RepLeftVert f hf) : p ∈ S0 f hf :=
  (Finset.mem_filter.mp hp).1

lemma repLeftArc_mem_S0 {p : ℍ} (hp : p ∈ RepLeftArc f hf) : p ∈ S0 f hf :=
  (Finset.mem_filter.mp hp).1

lemma repCanon_mem_S0 {p : ℍ} (hp : p ∈ RepCanon f hf) : p ∈ S0 f hf := by
  simp only [RepCanon, Finset.mem_union] at hp
  rcases hp with (h | h) | h
  · exact repStrict_mem_S0 f hf h
  · exact repLeftVert_mem_S0 f hf h
  · exact repLeftArc_mem_S0 f hf h

lemma repCanon_mem_fd {p : ℍ} (hp : p ∈ RepCanon f hf) : p ∈ 𝒟' :=
  S0_mem_fd f hf p (repCanon_mem_S0 f hf hp)

/-! ## Orbit Equality Helpers -/

/-- T⁻¹-translation preserves orbits: `orb((-1)+ᵥp) = orb(p)`. -/
lemma orb_vAdd_neg_one_eq (p : ℍ) : orb ((-1 : ℝ) +ᵥ p) = orb p := by
  have h_eq : ModularGroup.T⁻¹ • p = (-1 : ℝ) +ᵥ p := by
    have h1 : ModularGroup.T • (ModularGroup.T⁻¹ • p) = p := smul_inv_smul _ p
    rw [UpperHalfPlane.modular_T_smul] at h1
    have h2 : ModularGroup.T⁻¹ • p =
        (-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ (ModularGroup.T⁻¹ • p)) := by
      rw [← add_vadd, show (-1 : ℝ) + 1 = 0 from by ring, zero_vadd]
    rwa [h1] at h2
  show Quotient.mk'' ((-1 : ℝ) +ᵥ p) = Quotient.mk'' p
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨ModularGroup.T⁻¹, h_eq⟩

/-- S-action preserves orbits: `orb(S • p) = orb(p)`. -/
lemma orb_S_smul_eq (p : ℍ) : orb (ModularGroup.S • p) = orb p := by
  show Quotient.mk'' (ModularGroup.S • p) = Quotient.mk'' p
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨ModularGroup.S, rfl⟩

/-! ## Unit Circle Characterization on ℍ -/

/-- On ℍ, ‖p‖ = 1 and re = 0 forces p = i. -/
private lemma uhp_norm_one_re_zero_eq_i (p : ℍ) (hn : ‖(p : ℂ)‖ = 1)
    (hr : (p : ℂ).re = 0) : p = ellipticPoint_i' := by
  apply Subtype.ext; show (p : ℂ) = I
  have h_nsq : Complex.normSq (p : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn, one_pow]
  rw [Complex.normSq_apply, hr] at h_nsq
  -- h_nsq : 0 * 0 + im * im = 1
  have h_sq : (p : ℂ).im * (p : ℂ).im = 1 := by linarith
  have h_prod : ((p : ℂ).im - 1) * ((p : ℂ).im + 1) = 0 := by
    have : ((p : ℂ).im - 1) * ((p : ℂ).im + 1) = (p : ℂ).im * (p : ℂ).im - 1 := by ring
    linarith
  have h_im : (p : ℂ).im = 1 := by
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · have h_pos : 0 < (p : ℂ).im := p.2; linarith
  apply Complex.ext
  · rw [hr]; exact Complex.I_re.symm
  · rw [h_im]; exact Complex.I_im.symm

/-- On ℍ, ‖p‖ = 1 and re = -1/2 forces p = ρ. -/
private lemma uhp_norm_one_re_neg_half_eq_rho (p : ℍ) (hn : ‖(p : ℂ)‖ = 1)
    (hr : (p : ℂ).re = -1/2) : p = ellipticPoint_rho' := by
  apply Subtype.ext; show (p : ℂ) = (ellipticPoint_rho' : ℂ)
  have h_nsq : Complex.normSq (p : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn, one_pow]
  rw [Complex.normSq_apply, hr] at h_nsq
  have h_im_sq : (p : ℂ).im * (p : ℂ).im = 3/4 := by nlinarith
  have h3 := Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)
  have h_prod : ((p : ℂ).im - Real.sqrt 3 / 2) * ((p : ℂ).im + Real.sqrt 3 / 2) = 0 := by
    nlinarith
  have h_im : (p : ℂ).im = Real.sqrt 3 / 2 := by
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos p.2 (by positivity)))
  have h_rho_re : (ellipticPoint_rho' : ℂ).re = -1/2 := by
    show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = -1/2
    simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]; norm_num
  have h_rho_im : (ellipticPoint_rho' : ℂ).im = Real.sqrt 3 / 2 := by
    show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).im = Real.sqrt 3 / 2
    simp only [add_im, mul_im, I_re, I_im, mul_one, neg_im, one_im, div_ofNat_im,
      ofReal_im, mul_zero, add_zero, neg_zero, zero_div, ofReal_re, div_ofNat_re, zero_add]
  apply Complex.ext
  · exact hr.trans h_rho_re.symm
  · exact h_im.trans h_rho_im.symm

/-- On ℍ, ‖p‖ = 1 and re = 1/2 forces p = ρ + 1. -/
private lemma uhp_norm_one_re_half_eq_rho_plus_one (p : ℍ) (hn : ‖(p : ℂ)‖ = 1)
    (hr : (p : ℂ).re = 1/2) : p = ellipticPoint_rho_plus_one' := by
  apply Subtype.ext; show (p : ℂ) = (ellipticPoint_rho_plus_one' : ℂ)
  have h_nsq : Complex.normSq (p : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn, one_pow]
  rw [Complex.normSq_apply, hr] at h_nsq
  have h_im_sq : (p : ℂ).im * (p : ℂ).im = 3/4 := by nlinarith
  have h3 := Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)
  have h_prod : ((p : ℂ).im - Real.sqrt 3 / 2) * ((p : ℂ).im + Real.sqrt 3 / 2) = 0 := by
    nlinarith
  have h_im : (p : ℂ).im = Real.sqrt 3 / 2 := by
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos p.2 (by positivity)))
  have h_rho1_re : (ellipticPoint_rho_plus_one' : ℂ).re = 1/2 := by
    show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = 1/2
    simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]; norm_num
  have h_rho1_im : (ellipticPoint_rho_plus_one' : ℂ).im = Real.sqrt 3 / 2 := by
    show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).im = Real.sqrt 3 / 2
    simp only [add_im, mul_im, I_re, I_im, mul_one, one_im, div_ofNat_im,
      ofReal_im, mul_zero, add_zero, zero_div, ofReal_re, div_ofNat_re, zero_add]
  apply Complex.ext
  · exact hr.trans h_rho1_re.symm
  · exact h_im.trans h_rho1_im.symm

/-! ## Main Existence Theorem -/

/-- Every non-elliptic orbit with nonzero order has a representative in `RepCanon`.

**Proof strategy:** Start with the FD' representative from `orbit_has_fd'_rep`.
Classify it by geometry (interior / vertical edge / arc) and "move to the left"
if it lands on the right vertical or right arc:
- Right vertical (`re = 1/2, ‖p‖ > 1`): apply `(-1)+ᵥ` (T⁻¹) to reach left vertical
- Right arc (`‖p‖ = 1, re > 0`): apply `S` to negate real part
- Left side / interior: already in `RepCanon` -/
theorem exists_repCanon_of_nonEllOrbit :
    ∀ q : NonEllOrbit,
      ordOrbit f q.val ≠ 0 →
      ∃ p ∈ RepCanon f hf, orb p = q.val := by
  intro q hord
  obtain ⟨hq_ne_i, hq_ne_rho⟩ := q.2
  -- Step 1: Get FD' representative
  obtain ⟨p0, hp0_orb, hp0_fd⟩ := orbit_has_fd'_rep q.val
  -- Step 2: p0 has nonzero order (lift from orbit order)
  have hp0_ord : orderOfVanishingAt' (⇑f) p0 ≠ 0 := by
    rw [← ordOrbit_mk f p0, hp0_orb]; exact hord
  -- Step 3: p0 ∈ S0 (in FD' with nonzero order)
  have hp0_S0 : p0 ∈ S0 f hf := S0_complete f hf p0 hp0_fd hp0_ord
  -- Step 4: p0 is not any elliptic point (from non-elliptic orbit)
  have hp0_ne_i : p0 ≠ ellipticPoint_i' := by
    intro h; rw [h] at hp0_orb; exact hq_ne_i hp0_orb.symm
  have hp0_ne_rho : p0 ≠ ellipticPoint_rho' := by
    intro h; rw [h] at hp0_orb; exact hq_ne_rho hp0_orb.symm
  have hp0_ne_rho1 : p0 ≠ ellipticPoint_rho_plus_one' := by
    intro h; rw [h] at hp0_orb
    exact hq_ne_rho (hp0_orb.symm.trans orb_rho_plus_one_eq_orb_rho)
  -- Step 5: FD' properties
  have h_abs_re := hp0_fd.1  -- |re(p0)| ≤ 1/2
  have h_norm := hp0_fd.2    -- ‖p0‖ ≥ 1
  -- Bridge: UpperHalfPlane.re = Complex.re
  have h_re_bridge : p0.re = (↑p0 : ℂ).re := rfl
  -- Step 6: Case split on ‖p0‖ > 1 vs ‖p0‖ = 1
  rcases h_norm.lt_or_eq with h_gt | h_eq
  · -- Case: 1 < ‖p0‖ (interior or vertical edge)
    rcases h_abs_re.lt_or_eq with h_re_lt | h_re_eq
    · -- Sub-case: |re| < 1/2 → p0 ∈ RepStrict
      refine ⟨p0, ?_, hp0_orb⟩
      simp only [RepCanon, Finset.mem_union]
      left; left
      exact Finset.mem_filter.mpr ⟨hp0_S0, hp0_ne_i, hp0_ne_rho, hp0_ne_rho1, h_gt,
        by rwa [h_re_bridge] at h_re_lt⟩
    · -- Sub-case: |re| = 1/2 → split on sign
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1/2)).mp h_re_eq with h_half | h_neg_half
      · -- re = 1/2: apply T⁻¹ to move to left vertical
        have h_half_coe : (↑p0 : ℂ).re = 1/2 := by rwa [← h_re_bridge]
        set p1 := (-1 : ℝ) +ᵥ p0
        have hp1_fd : p1 ∈ 𝒟' := vAdd_neg_one_mem_fd_of_right_vert p0 hp0_fd h_half_coe
        have hp1_ord : orderOfVanishingAt' (⇑f) p1 ≠ 0 := by
          show orderOfVanishingAt' (⇑f) ((-1 : ℝ) +ᵥ p0) ≠ 0
          rw [ord_vAdd_neg_one_eq f p0]; exact hp0_ord
        have hp1_S0 : p1 ∈ S0 f hf := S0_complete f hf p1 hp1_fd hp1_ord
        have hp1_re : (↑p1 : ℂ).re = -1/2 := by
          show ((-1 : ℝ) +ᵥ p0 : ℍ).val.re = -1/2
          rw [vAdd_neg_one_coe, sub_re, one_re]; linarith [h_half_coe]
        have hp1_norm : ‖(↑p1 : ℂ)‖ > 1 := by
          show ‖((-1 : ℝ) +ᵥ p0 : ℍ).val‖ > 1
          rw [vAdd_neg_one_norm_eq_of_re_half p0 h_half_coe]; exact h_gt
        have hp1_orb : orb p1 = q.val := by
          show orb ((-1 : ℝ) +ᵥ p0) = q.val
          rw [orb_vAdd_neg_one_eq]; exact hp0_orb
        refine ⟨p1, ?_, hp1_orb⟩
        simp only [RepCanon, Finset.mem_union]
        left; right
        exact Finset.mem_filter.mpr ⟨hp1_S0, hp1_re, hp1_norm⟩
      · -- re = -(1/2): already on left vertical
        have h_re : (↑p0 : ℂ).re = -1/2 := by rw [← h_re_bridge]; linarith
        refine ⟨p0, ?_, hp0_orb⟩
        simp only [RepCanon, Finset.mem_union]
        left; right
        exact Finset.mem_filter.mpr ⟨hp0_S0, h_re, h_gt⟩
  · -- Case: 1 = ‖p0‖, i.e., p0 on unit circle
    have h_norm_eq : ‖(↑p0 : ℂ)‖ = 1 := h_eq.symm
    -- Non-elliptic excludes i, ρ, ρ+1 → re ∉ {0, -1/2, 1/2}
    have h_re_ne_zero : (↑p0 : ℂ).re ≠ 0 :=
      fun h => hp0_ne_i (uhp_norm_one_re_zero_eq_i p0 h_norm_eq h)
    have h_re_ne_neg_half : (↑p0 : ℂ).re ≠ -1/2 :=
      fun h => hp0_ne_rho (uhp_norm_one_re_neg_half_eq_rho p0 h_norm_eq h)
    have h_re_ne_half : (↑p0 : ℂ).re ≠ 1/2 :=
      fun h => hp0_ne_rho1 (uhp_norm_one_re_half_eq_rho_plus_one p0 h_norm_eq h)
    -- From |re| ≤ 1/2 and re ∉ {-1/2, 1/2}: |re| < 1/2
    have h_re_strict : |p0.re| < 1/2 := by
      rcases h_abs_re.lt_or_eq with h | h
      · exact h
      · exfalso
        rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1/2)).mp h with h' | h'
        · exact h_re_ne_half (by rwa [← h_re_bridge])
        · exact h_re_ne_neg_half (by rw [← h_re_bridge]; linarith)
    -- Split on re < 0 vs re > 0
    rcases lt_or_gt_of_ne h_re_ne_zero with h_neg | h_pos
    · -- re < 0: p0 ∈ RepLeftArc
      refine ⟨p0, ?_, hp0_orb⟩
      simp only [RepCanon, Finset.mem_union]
      right
      exact Finset.mem_filter.mpr ⟨hp0_S0, hp0_ne_rho, h_norm_eq, h_neg⟩
    · -- re > 0: apply S to flip to left arc
      set p1 := ModularGroup.S • p0
      have hp1_fd : p1 ∈ 𝒟' := S_smul_mem_fd_of_unit p0 hp0_fd h_norm_eq
      have hp1_ord : orderOfVanishingAt' (⇑f) p1 ≠ 0 := by
        show orderOfVanishingAt' (⇑f) (ModularGroup.S • p0) ≠ 0
        rw [ord_S_eq f p0]; exact hp0_ord
      have hp1_S0 : p1 ∈ S0 f hf := S0_complete f hf p1 hp1_fd hp1_ord
      have hp1_norm : ‖(↑p1 : ℂ)‖ = 1 := S_smul_norm_of_unit p0 h_norm_eq
      have hp1_re_neg : (↑p1 : ℂ).re < 0 := by
        have h1 : (ModularGroup.S • p0 : ℍ).re = -p0.re :=
          S_smul_re_neg_of_unit p0 h_norm_eq
        show (ModularGroup.S • p0 : ℍ).val.re < 0
        rw [show (ModularGroup.S • p0 : ℍ).val.re =
          (ModularGroup.S • p0 : ℍ).re from rfl, h1]
        linarith [h_re_bridge]
      have hp1_ne_rho : p1 ≠ ellipticPoint_rho' := by
        intro h
        have h1 : orb p1 = orho := h ▸ rfl
        have h2 : orb p1 = q.val := by
          show orb (ModularGroup.S • p0) = q.val
          rw [orb_S_smul_eq]; exact hp0_orb
        exact hq_ne_rho (h2.symm.trans h1)
      have hp1_orb : orb p1 = q.val := by
        show orb (ModularGroup.S • p0) = q.val
        rw [orb_S_smul_eq]; exact hp0_orb
      refine ⟨p1, ?_, hp1_orb⟩
      simp only [RepCanon, Finset.mem_union]
      right
      exact Finset.mem_filter.mpr ⟨hp1_S0, hp1_ne_rho, hp1_norm, hp1_re_neg⟩

/-! ## Support Cover Lemma -/

/-- The support of the non-elliptic orbit summand is contained in the
image of `RepCanon` under `orb`. This is the key lemma Worker B needs
to rewrite `∑ᶠ` over orbits as a `Finset.sum` over `RepCanon`. -/
theorem support_ordOrbit_nonEll_subset :
    ∀ q : NonEllOrbit,
      (ordOrbit f q.val : ℂ) ≠ 0 →
      q.val ∈ ((RepCanon f hf).image orb : Finset Orbit) := by
  intro q hord
  have hord_int : ordOrbit f q.val ≠ 0 := by exact_mod_cast hord
  obtain ⟨p, hp_mem, hp_orb⟩ := exists_repCanon_of_nonEllOrbit f hf q hord_int
  exact Finset.mem_image.mpr ⟨p, hp_mem, hp_orb⟩

end
