/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormulaDefinitions
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ResidueSide

/-!
# Orbit Pairing Lemmas for the Valence Formula

Pure-algebra lemmas about orbit pairings under the modular group actions:
- **T** (translation by 1): `z ↦ z + 1`
- **S** (inversion): `z ↦ -1/z`

These are used downstream to collapse the explicit coefficient expansion
of the valence formula (eliminating `h_T_inv` hypotheses, pairing left/right
vertical contributions, pairing left/right arc contributions).

## Main Results

### T-translation (`z ↦ z + 1`)

* `vAdd_one_coe`: `((1:ℝ) +ᵥ p : ℂ) = (p : ℂ) + 1`
* `vAdd_one_rho_eq_rho_plus_one`: `(1:ℝ) +ᵥ ρ' = ρ'+1` as ℍ elements
* `ord_rho_plus_one_eq_ord_rho`: `ord(f, ρ+1) = ord(f, ρ)`
* `vAdd_one_re`: real part shifts by 1
* `vAdd_one_im_eq`: imaginary part preserved
* `vAdd_one_norm_eq_of_re_neg_half`: norm preserved when `re = -1/2`
* `vAdd_one_mem_fd_of_left_vert`: left-vert FD points map to right-vert FD points

### S-action (`z ↦ -1/z`)

* `S_smul_norm_of_unit`: `‖z‖ = 1 → ‖S·z‖ = 1`
* `S_smul_re_neg_of_unit`: `‖z‖ = 1 → (S·z).re = -z.re`

### Vertical Pairing

* `sum_ord_leftVert_eq_sum_ord_rightVert`: Orders on left vertical edge
  equal orders on right vertical edge (via T-invariance).
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## T-translation Basics -/

/-- Coercion identity for T-translation: `((1:ℝ) +ᵥ p : ℂ) = (p : ℂ) + 1`. -/
lemma vAdd_one_coe (p : ℍ) : ((1 : ℝ) +ᵥ p : ℍ).val = (p : ℂ) + 1 := by
  show ((1 : ℝ) : ℂ) + (p : ℂ) = (p : ℂ) + 1; push_cast; ring

/-- T-translation shifts real part by 1. -/
lemma vAdd_one_re (p : ℍ) : ((1 : ℝ) +ᵥ p : ℍ).re = p.re + 1 := by
  show ((1 : ℝ) +ᵥ p : ℍ).val.re = p.re + 1
  rw [vAdd_one_coe]; simp [add_re]

/-- T-translation preserves imaginary part. -/
lemma vAdd_one_im_eq (p : ℍ) : ((1 : ℝ) +ᵥ p : ℍ).im = p.im := by
  show ((1 : ℝ) +ᵥ p : ℍ).val.im = p.im
  rw [vAdd_one_coe]; simp [add_im]

/-- T⁻¹-translation coercion: `((-1:ℝ) +ᵥ p : ℂ) = (p : ℂ) - 1`. -/
lemma vAdd_neg_one_coe (p : ℍ) : ((-1 : ℝ) +ᵥ p : ℍ).val = (p : ℂ) - 1 := by
  show ((-1 : ℝ) : ℂ) + (p : ℂ) = (p : ℂ) - 1; push_cast; ring

/-- T⁻¹-translation shifts real part by -1. -/
lemma vAdd_neg_one_re (p : ℍ) : ((-1 : ℝ) +ᵥ p : ℍ).re = p.re - 1 := by
  show ((-1 : ℝ) +ᵥ p : ℍ).val.re = p.re - 1
  rw [vAdd_neg_one_coe]; simp [sub_re]

/-- T⁻¹-translation preserves imaginary part. -/
lemma vAdd_neg_one_im_eq (p : ℍ) : ((-1 : ℝ) +ᵥ p : ℍ).im = p.im := by
  show ((-1 : ℝ) +ᵥ p : ℍ).val.im = p.im
  rw [vAdd_neg_one_coe]; simp [sub_im]

/-! ## Norm Preservation under T-translation -/

/-- When `z.re = -1/2`, we have `‖z + 1‖ = ‖z‖` (since `(-1/2)² = (1/2)²`). -/
lemma norm_add_one_eq_of_re_neg_half (z : ℂ) (hre : z.re = -1/2) :
    ‖z + 1‖ = ‖z‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  have him : (z + 1).im = z.im := by simp [add_im]
  have hre' : (z + 1).re = 1/2 := by simp [add_re, hre]; norm_num
  rw [him, hre', hre]; ring

/-- When `z.re = 1/2`, we have `‖z - 1‖ = ‖z‖` (since `(1/2)² = (-1/2)²`). -/
lemma norm_sub_one_eq_of_re_half (z : ℂ) (hre : z.re = 1/2) :
    ‖z - 1‖ = ‖z‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  have him : (z - 1).im = z.im := by simp [sub_im]
  have hre' : (z - 1).re = -1/2 := by simp [sub_re, hre]; norm_num
  rw [him, hre', hre]; ring

/-- T-translation preserves norm for left-vertical points (`re = -1/2`). -/
lemma vAdd_one_norm_eq_of_re_neg_half (p : ℍ)
    (hre : (p : ℂ).re = -1/2) :
    ‖((1 : ℝ) +ᵥ p : ℍ).val‖ = ‖(p : ℂ)‖ := by
  rw [vAdd_one_coe]; exact norm_add_one_eq_of_re_neg_half _ hre

/-- T⁻¹-translation preserves norm for right-vertical points (`re = 1/2`). -/
lemma vAdd_neg_one_norm_eq_of_re_half (p : ℍ)
    (hre : (p : ℂ).re = 1/2) :
    ‖((-1 : ℝ) +ᵥ p : ℍ).val‖ = ‖(p : ℂ)‖ := by
  rw [vAdd_neg_one_coe]; exact norm_sub_one_eq_of_re_half _ hre

/-! ## Fundamental Domain Membership under T-translation -/

/-- T-translation sends left-vertical FD points to the standard FD:
if `p ∈ 𝒟'` with `p.re = -1/2` then `(1:ℝ) +ᵥ p ∈ 𝒟'`. -/
theorem vAdd_one_mem_fd_of_left_vert (p : ℍ)
    (hp_fd : p ∈ 𝒟') (hre : (p : ℂ).re = -1/2) :
    (1 : ℝ) +ᵥ p ∈ 𝒟' := by
  obtain ⟨habs_re, hnorm⟩ := hp_fd
  constructor
  · -- |re| ≤ 1/2: re of (1 +ᵥ p) = p.re + 1 = 1/2
    show |((1 : ℝ) +ᵥ p : ℍ).val.re| ≤ 1 / 2
    rw [vAdd_one_coe, add_re, one_re, hre]; norm_num
  · -- ‖(1 +ᵥ p)‖ ≥ 1: norm preserved
    show ‖((1 : ℝ) +ᵥ p : ℍ).val‖ ≥ 1
    rw [vAdd_one_norm_eq_of_re_neg_half p hre]; exact hnorm

/-- T⁻¹-translation sends right-vertical FD points to the standard FD:
if `p ∈ 𝒟'` with `p.re = 1/2` then `(-1:ℝ) +ᵥ p ∈ 𝒟'`. -/
theorem vAdd_neg_one_mem_fd_of_right_vert (p : ℍ)
    (hp_fd : p ∈ 𝒟') (hre : (p : ℂ).re = 1/2) :
    (-1 : ℝ) +ᵥ p ∈ 𝒟' := by
  obtain ⟨habs_re, hnorm⟩ := hp_fd
  constructor
  · show |((-1 : ℝ) +ᵥ p : ℍ).val.re| ≤ 1 / 2
    rw [vAdd_neg_one_coe, sub_re, one_re, hre]; norm_num
  · show ‖((-1 : ℝ) +ᵥ p : ℍ).val‖ ≥ 1
    rw [vAdd_neg_one_norm_eq_of_re_half p hre]; exact hnorm

/-! ## Elliptic Points: ρ and ρ+1 -/

/-- `(1:ℝ) +ᵥ ρ' = ρ'+1` as UpperHalfPlane elements.
This is the key identity connecting the T-action with the elliptic point definitions. -/
theorem vAdd_one_rho_eq_rho_plus_one :
    (1 : ℝ) +ᵥ ellipticPoint_rho' = ellipticPoint_rho_plus_one' := by
  apply Subtype.ext
  rw [vAdd_one_coe]
  exact ellipticPoint_rho_add_one_eq

/-- `(-1:ℝ) +ᵥ (ρ'+1) = ρ'` as UpperHalfPlane elements. -/
theorem vAdd_neg_one_rho_plus_one_eq_rho :
    (-1 : ℝ) +ᵥ ellipticPoint_rho_plus_one' = ellipticPoint_rho' := by
  apply Subtype.ext
  rw [vAdd_neg_one_coe, sub_eq_iff_eq_add]
  exact ellipticPoint_rho_add_one_eq.symm

/-- ρ+1 is in the standard fundamental domain 𝒟'. -/
theorem ellipticPoint_rho_plus_one_mem_fd' : ellipticPoint_rho_plus_one' ∈ 𝒟' := by
  rw [← vAdd_one_rho_eq_rho_plus_one]
  exact vAdd_one_mem_fd_of_left_vert ellipticPoint_rho' ellipticPoint_rho_mem_fd'
    (by simp [ellipticPoint_rho'])

/-! ## Order Invariance Specializations -/

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-- `ord(f, ρ+1) = ord(f, ρ)` via the T-translation identity `vAdd_one_rho_eq_rho_plus_one`.
(Also available as `ord_rho_plus_one_eq_ord_rho` from `ValenceFormula_ResidueSide`.) -/
theorem ord_rho_plus_one_eq_ord_rho_via_vAdd :
    orderOfVanishingAt' (⇑f) ellipticPoint_rho_plus_one' =
    orderOfVanishingAt' (⇑f) ellipticPoint_rho' := by
  rw [← vAdd_one_rho_eq_rho_plus_one]
  exact ord_add_one_eq f ellipticPoint_rho'

/-! ## S-action Geometry -/

/-- S-action coe: `(S·z : ℂ) = (-z)⁻¹`. -/
lemma S_smul_coe (p : ℍ) : (ModularGroup.S • p : ℍ).val = (-(p : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]; rfl

/-- S-action preserves norm on the unit circle: `‖z‖ = 1 → ‖S·z‖ = 1`. -/
theorem S_smul_norm_of_unit (p : ℍ) (hp : ‖(p : ℂ)‖ = 1) :
    ‖(ModularGroup.S • p : ℍ).val‖ = 1 := by
  rw [S_smul_coe, norm_inv, norm_neg, hp, inv_one]

/-- S-action negates real part on the unit circle: if `‖z‖ = 1`, then `(S·z).re = -z.re`. -/
theorem S_smul_re_neg_of_unit (p : ℍ) (hp : ‖(p : ℂ)‖ = 1) :
    (ModularGroup.S • p : ℍ).re = -p.re := by
  have hp_ne : (p : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hp; norm_num at hp
  have hns : Complex.normSq (p : ℂ) = 1 := by
    rw [← Complex.sq_norm, hp]; norm_num
  show (ModularGroup.S • p : ℍ).val.re = -p.re
  rw [S_smul_coe]
  simp only [Complex.inv_re, Complex.neg_re, Complex.normSq_neg, hns, div_one]
  rfl

/-- S-action preserves the fundamental domain for unit-circle points with `|re| ≤ 1/2`.
More precisely: if `p ∈ 𝒟'` and `‖p‖ = 1`, then `S·p ∈ 𝒟'`. -/
theorem S_smul_mem_fd_of_unit (p : ℍ) (hp_fd : p ∈ 𝒟') (hp_norm : ‖(p : ℂ)‖ = 1) :
    ModularGroup.S • p ∈ 𝒟' := by
  obtain ⟨habs_re, _⟩ := hp_fd
  constructor
  · -- |re(S·p)| = |-re(p)| = |re(p)| ≤ 1/2
    rw [show (ModularGroup.S • p : ℍ).re = (ModularGroup.S • p : ℍ).val.re from rfl]
    rw [S_smul_coe]
    simp only [Complex.inv_re, Complex.neg_re, Complex.normSq_neg]
    have hns : Complex.normSq (p : ℂ) = 1 := by
      rw [← Complex.sq_norm, hp_norm]; norm_num
    rw [hns, div_one, abs_neg]
    exact habs_re
  · -- ‖S·p‖ = 1 ≥ 1
    show ‖(ModularGroup.S • p : ℍ).val‖ ≥ 1
    rw [S_smul_norm_of_unit p hp_norm]

/-! ## Vertical Pairing via T-translation -/

/-- The left-vertical filter of S: points with `re = -1/2` and `‖p‖ > 1`. -/
def S_leftVert (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => (p : ℂ).re = -1/2 ∧ ‖(p : ℂ)‖ > 1)

/-- The right-vertical filter of S: points with `re = 1/2` and `‖p‖ > 1`. -/
def S_rightVert (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => (p : ℂ).re = 1/2 ∧ ‖(p : ℂ)‖ > 1)

/-- T-translation maps `S_leftVert S` into `S_rightVert S` (when S is complete in 𝒟'). -/
theorem vAdd_one_leftVert_subset_rightVert (S : Finset ℍ)
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∀ p ∈ S_leftVert S,
      orderOfVanishingAt' (⇑f) p ≠ 0 →
      (1 : ℝ) +ᵥ p ∈ S_rightVert S := by
  intro p hp hord
  simp only [S_leftVert, Finset.mem_filter] at hp
  obtain ⟨_, hre, hnorm⟩ := hp
  have hp_fd : p ∈ 𝒟' := by
    constructor
    · rw [show p.re = (p : ℂ).re from rfl, hre]; norm_num
    · exact le_of_lt hnorm
  have hp1_fd := vAdd_one_mem_fd_of_left_vert p hp_fd hre
  have hp1_ord : orderOfVanishingAt' (⇑f) ((1 : ℝ) +ᵥ p) ≠ 0 := by
    rwa [ord_add_one_eq f p]
  have hp1_in_S := hS_complete _ hp1_fd hp1_ord
  simp only [S_rightVert, Finset.mem_filter]
  refine ⟨hp1_in_S, ?_, ?_⟩
  · -- re = 1/2: use vAdd_one_coe for the computation
    show ((1 : ℝ) +ᵥ p : ℍ).val.re = 1 / 2
    rw [vAdd_one_coe, add_re, one_re]; linarith [hre]
  · -- ‖·‖ > 1: norm preserved under T for re = -1/2
    show ‖((1 : ℝ) +ᵥ p : ℍ).val‖ > 1
    rw [vAdd_one_norm_eq_of_re_neg_half p hre]; exact hnorm

/-- The sum of orders on `S_leftVert S` equals the sum of the T-translated orders.
Combined with T-invariance (`ord_add_one_eq`), this equals the sum on `S_rightVert S`
when the image lies in `S_rightVert S`. -/
theorem sum_ord_leftVert_eq_sum_T_image (S : Finset ℍ) :
    ∑ p ∈ S_leftVert S, (orderOfVanishingAt' (⇑f) p : ℂ) =
    ∑ p ∈ S_leftVert S, (orderOfVanishingAt' (⇑f) ((1 : ℝ) +ᵥ p) : ℂ) :=
  Finset.sum_congr rfl fun p _ => by rw [ord_add_one_eq f p]

/-! ## T⁻¹-invariance of Order -/

/-- T⁻¹-invariance of vanishing order: `ord(f, (-1)+ᵥp) = ord(f, p)`. -/
lemma ord_vAdd_neg_one_eq (p : ℍ) :
    orderOfVanishingAt' (⇑f) ((-1 : ℝ) +ᵥ p) = orderOfVanishingAt' (⇑f) p := by
  have h := ord_add_one_eq f ((-1 : ℝ) +ᵥ p)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ p) = p from by
    ext; show ((1 : ℝ) : ℂ) + (((-1 : ℝ) : ℂ) + (p : ℂ)) = (p : ℂ); push_cast; ring] at h
  exact h.symm

/-! ## Arc Filters -/

/-- The left-arc filter: points on the unit circle with negative real part. -/
def S_leftArc (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)

/-- The right-arc filter: points on the unit circle with positive real part. -/
def S_rightArc (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0)

/-! ## S² = id on ℍ -/

/-- S² = -1 in SL(2,ℤ). -/
private lemma S_mul_S : ModularGroup.S * ModularGroup.S = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]

/-- S² acts as the identity on ℍ (since -I acts trivially). -/
lemma S_smul_S_smul (p : ℍ) : ModularGroup.S • (ModularGroup.S • p) = p := by
  rw [← mul_smul, S_mul_S]; apply Subtype.ext; simp

/-- The S-action is injective on ℍ. -/
lemma S_smul_injective : Function.Injective (ModularGroup.S • · : ℍ → ℍ) :=
  Function.HasLeftInverse.injective ⟨(ModularGroup.S • ·), S_smul_S_smul⟩

/-! ## Vertical Pairing: ∑ rightVert = ∑ leftVert -/

private lemma ord_ne_zero_of_cast_ne_zero {p : ℍ} {f : ℍ → ℂ}
    (h : (orderOfVanishingAt' f p : ℂ) ≠ 0) : orderOfVanishingAt' f p ≠ 0 := by
  exact_mod_cast h

/-- The sum of orders on the right vertical edge equals the sum on the left vertical edge.
This uses T⁻¹ as a bijection from nonzero-order right-vert points to left-vert points. -/
theorem sum_ord_rightVert_eq_sum_ord_leftVert (S : Finset ℍ)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∑ p ∈ S_rightVert S, (orderOfVanishingAt' (⇑f) p : ℂ) =
    ∑ p ∈ S_leftVert S, (orderOfVanishingAt' (⇑f) p : ℂ) := by
  -- Filter to nonzero-order points (zero-order terms contribute 0)
  rw [← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero (s := S_leftVert S)]
  -- Build bijection (-1:ℝ) +ᵥ · from rightVert∩{ord≠0} to leftVert∩{ord≠0}
  apply Finset.sum_nbij ((-1 : ℝ) +ᵥ ·)
  · -- Maps rightVert∩{ord≠0} → leftVert∩{ord≠0}
    intro p hp
    simp only [Finset.mem_filter, S_rightVert, S_leftVert] at hp ⊢
    obtain ⟨⟨hp_S, hre, hnorm⟩, hord⟩ := hp
    have hp_fd := hS p hp_S
    have hp_fd' := vAdd_neg_one_mem_fd_of_right_vert p hp_fd hre
    have hord_int := ord_ne_zero_of_cast_ne_zero hord
    have hord' : orderOfVanishingAt' (⇑f) ((-1 : ℝ) +ᵥ p) ≠ 0 := by
      rw [ord_vAdd_neg_one_eq f p]; exact hord_int
    refine ⟨⟨hS_complete _ hp_fd' hord', ?_, ?_⟩, ?_⟩
    · show ((-1 : ℝ) +ᵥ p : ℍ).val.re = -1 / 2
      rw [vAdd_neg_one_coe, sub_re, one_re, hre]; norm_num
    · show ‖((-1 : ℝ) +ᵥ p : ℍ).val‖ > 1
      rw [vAdd_neg_one_norm_eq_of_re_half p hre]; exact hnorm
    · show (orderOfVanishingAt' (⇑f) ((-1 : ℝ) +ᵥ p) : ℂ) ≠ 0
      rw [show orderOfVanishingAt' (⇑f) ((-1 : ℝ) +ᵥ p) =
        orderOfVanishingAt' (⇑f) p from ord_vAdd_neg_one_eq f p]; exact hord
  · -- Injective
    intro a _ b _ h; exact vadd_left_cancel (-1 : ℝ) h
  · -- Surjective
    intro q hq
    rw [Finset.mem_coe] at hq
    simp only [Finset.mem_filter, S_leftVert] at hq
    obtain ⟨⟨hq_S, hre, hnorm⟩, hord⟩ := hq
    have hq_fd := hS q hq_S
    have hord_int := ord_ne_zero_of_cast_ne_zero hord
    refine ⟨(1 : ℝ) +ᵥ q, ?_, ?_⟩
    · rw [Finset.mem_coe]; simp only [Finset.mem_filter, S_rightVert]
      have hq_fd' := vAdd_one_mem_fd_of_left_vert q hq_fd hre
      have hord' : orderOfVanishingAt' (⇑f) ((1 : ℝ) +ᵥ q) ≠ 0 := by
        rw [ord_add_one_eq f q]; exact hord_int
      refine ⟨⟨hS_complete _ hq_fd' hord', ?_, ?_⟩, ?_⟩
      · show ((1 : ℝ) +ᵥ q : ℍ).val.re = 1 / 2
        rw [vAdd_one_coe, add_re, one_re, hre]; norm_num
      · show ‖((1 : ℝ) +ᵥ q : ℍ).val‖ > 1
        rw [vAdd_one_norm_eq_of_re_neg_half q hre]; exact hnorm
      · show (orderOfVanishingAt' (⇑f) ((1 : ℝ) +ᵥ q) : ℂ) ≠ 0
        rw [show orderOfVanishingAt' (⇑f) ((1 : ℝ) +ᵥ q) =
          orderOfVanishingAt' (⇑f) q from ord_add_one_eq f q]; exact hord
    · -- (-1) +ᵥ ((1) +ᵥ q) = q
      change (-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ q) = q
      rw [← add_vadd, show (-1 : ℝ) + 1 = 0 from by ring, zero_vadd]
  · -- Values equal: ord(p) = ord((-1)+ᵥp)
    intro p _
    show (orderOfVanishingAt' (⇑f) p : ℂ) = (orderOfVanishingAt' (⇑f) ((-1 : ℝ) +ᵥ p) : ℂ)
    rw [ord_vAdd_neg_one_eq f p]

/-! ## Arc Pairing: ∑ rightArc = ∑ leftArc -/

/-- The sum of orders on the right arc equals the sum on the left arc.
This uses S as a bijection from nonzero-order right-arc points to left-arc points. -/
theorem sum_ord_rightArc_eq_sum_ord_leftArc (S : Finset ℍ)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∑ p ∈ S_rightArc S, (orderOfVanishingAt' (⇑f) p : ℂ) =
    ∑ p ∈ S_leftArc S, (orderOfVanishingAt' (⇑f) p : ℂ) := by
  rw [← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero (s := S_leftArc S)]
  apply Finset.sum_nbij (ModularGroup.S • ·)
  · -- Maps rightArc∩{ord≠0} → leftArc∩{ord≠0}
    intro p hp
    simp only [Finset.mem_filter, S_rightArc, S_leftArc] at hp ⊢
    obtain ⟨⟨hp_S, hnorm, hre_pos⟩, hord⟩ := hp
    have hp_fd := hS p hp_S
    have hord_int := ord_ne_zero_of_cast_ne_zero hord
    have hSp_fd := S_smul_mem_fd_of_unit p hp_fd hnorm
    have hSp_norm := S_smul_norm_of_unit p hnorm
    have hSp_re := S_smul_re_neg_of_unit p hnorm
    have hord' : orderOfVanishingAt' (⇑f) (ModularGroup.S • p) ≠ 0 := by
      rw [ord_S_eq f p]; exact hord_int
    refine ⟨⟨hS_complete _ hSp_fd hord', hSp_norm, ?_⟩, ?_⟩
    · have hre_pos' : (↑p : ℂ).re > 0 := hre_pos
      have : (↑(ModularGroup.S • p) : ℂ).re = -(↑p : ℂ).re := by
        show (ModularGroup.S • p : ℍ).val.re = _
        rw [show (ModularGroup.S • p : ℍ).val.re = (ModularGroup.S • p : ℍ).re from rfl,
          hSp_re]; rfl
      linarith
    · show (orderOfVanishingAt' (⇑f) (ModularGroup.S • p) : ℂ) ≠ 0
      rw [show orderOfVanishingAt' (⇑f) (ModularGroup.S • p) =
        orderOfVanishingAt' (⇑f) p from ord_S_eq f p]; exact hord
  · -- Injective
    exact S_smul_injective.injOn
  · -- Surjective
    intro q hq
    rw [Finset.mem_coe] at hq
    simp only [Finset.mem_filter, S_leftArc] at hq
    obtain ⟨⟨hq_S, hnorm, hre_neg⟩, hord⟩ := hq
    have hq_fd := hS q hq_S
    have hord_int := ord_ne_zero_of_cast_ne_zero hord
    refine ⟨ModularGroup.S • q, ?_, S_smul_S_smul q⟩
    rw [Finset.mem_coe]; simp only [Finset.mem_filter, S_rightArc]
    have hSq_fd := S_smul_mem_fd_of_unit q hq_fd hnorm
    have hSq_norm := S_smul_norm_of_unit q hnorm
    have hSq_re := S_smul_re_neg_of_unit q hnorm
    have hord' : orderOfVanishingAt' (⇑f) (ModularGroup.S • q) ≠ 0 := by
      rw [ord_S_eq f q]; exact hord_int
    refine ⟨⟨hS_complete _ hSq_fd hord', hSq_norm, ?_⟩, ?_⟩
    · have hre_neg' : (↑q : ℂ).re < 0 := hre_neg
      have : (↑(ModularGroup.S • q) : ℂ).re = -(↑q : ℂ).re := by
        show (ModularGroup.S • q : ℍ).val.re = _
        rw [show (ModularGroup.S • q : ℍ).val.re = (ModularGroup.S • q : ℍ).re from rfl,
          hSq_re]; rfl
      linarith
    · show (orderOfVanishingAt' (⇑f) (ModularGroup.S • q) : ℂ) ≠ 0
      rw [show orderOfVanishingAt' (⇑f) (ModularGroup.S • q) =
        orderOfVanishingAt' (⇑f) q from ord_S_eq f q]; exact hord
  · -- Values equal: ord(p) = ord(S·p)
    intro p _
    show (orderOfVanishingAt' (⇑f) p : ℂ) = (orderOfVanishingAt' (⇑f) (ModularGroup.S • p) : ℂ)
    rw [ord_S_eq f p]

end
