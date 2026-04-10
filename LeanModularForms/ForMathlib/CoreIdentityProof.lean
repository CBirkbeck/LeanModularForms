/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.ResidueModularProof
import LeanModularForms.ValenceFormula.CoreIdentity

/-!
# Core Identity Proof -- Discharging `h_identity_for_zeros`

This file proves the winding-form identity that fills the last remaining hypothesis
(`h_identity_for_zeros`) of `ResidueModularData`, completing the valence formula chain.

## Strategy

The identity states: for any finite set `S_0 \subseteq D` capturing all zeros of `f`,

$$\mathrm{ord}_\infty(f) + \sum_{s \in S_0} (-\mathrm{gWN}(s)) \cdot \mathrm{ord}(f,s)
  = \frac{k}{12}$$

where `gWN` is the generalized winding number of the FD boundary (as a `PiecewiseC1Path`)
around `s`.

The proof proceeds in two stages:

**Stage 1** (winding_sum_eq_explicit): Show that for `FDWindingDataFull H` with all zeros
below height `H`, the winding-weighted sum `sum (-gWN * ord)` equals the explicit-coefficient
form:

  `(1/2) * ord(i) + (1/3) * ord(rho) + sum_strict_int + sum_left_vert + sum_left_arc`

This uses only the known winding number values from `FDWindingDataFull`:
- Interior: `gWN = -1`
- At `i`: `gWN = -1/2`
- At `rho`, `rho+1`: `gWN = -1/6`
- Smooth boundary: `gWN = -1/2`
Plus orbit pairing (T-invariance collapses verticals, S-invariance collapses arcs,
`ord(rho+1) = ord(rho)`).

**Stage 2** (coreIdentityProof): Combine Stage 1 with `valence_formula_orbit_sum` from
`CoreIdentity.lean` (which proves the explicit-coefficient form equals `k/12`) to obtain
the winding-form identity.

## Main results

* `winding_sum_eq_explicit` -- Stage 1: winding sum = explicit-coefficient form
* `coreIdentityProof` -- the winding-form identity for any zero set
* `mk_residueModularData_unconditional` -- fully discharged `ResidueModularData`
* `valence_formula_unconditional` -- the textbook valence formula, no hypotheses

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Chapter 3
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ### Auxiliary lemmas for point classification -/

omit f hf in
private lemma ellipticPointRho_re_neg' : (ellipticPointRho' : ℂ).re < 0 := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re < 0
  simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]; norm_num

omit f hf in
private lemma ellipticPointRhoPlusOne_re_pos' :
    (ellipticPointRhoPlusOne' : ℂ).re > 0 := by
  change (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re > 0
  simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]; norm_num

omit f hf in
private lemma ellipticPoint_ne_iρ1' : ellipticPointI' ≠ ellipticPointRhoPlusOne' := by
  intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
  simp [ellipticPointI', ellipticPointRhoPlusOne'] at this

omit f hf in
private lemma ellipticPoint_ne_ρρ1' : ellipticPointRho' ≠ ellipticPointRhoPlusOne' := by
  intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
  simp [ellipticPointRho', ellipticPointRhoPlusOne'] at this; norm_num at this

omit f hf in
private lemma unit_circle_re_neg_half_eq_rho' (s : ℍ)
    (hs_norm : ‖(s : ℂ)‖ = 1) (hs_re : (s : ℂ).re = -1/2) : s = ellipticPointRho' := by
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re] at h_nsq
  have h_im : (s : ℂ).im = Real.sqrt 3 / 2 := by
    have h_prod : ((s : ℂ).im - Real.sqrt 3 / 2) *
        ((s : ℂ).im + Real.sqrt 3 / 2) = 0 := by
      nlinarith [Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos s.2 (by positivity)))
  apply UpperHalfPlane.ext; apply Complex.ext <;>
    simp only [ellipticPointRho', UpperHalfPlane.coe_mk, add_re, add_im, neg_re, neg_im, one_re,
      one_im, div_ofNat_re, div_ofNat_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add, zero_div, neg_zero] <;>
    linarith

omit f hf in
private lemma unit_circle_re_pos_half_eq_rho_plus_one' (s : ℍ)
    (hs_norm : ‖(s : ℂ)‖ = 1) (hs_re : (s : ℂ).re = 1/2) :
    s = ellipticPointRhoPlusOne' := by
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re] at h_nsq
  have h_im : (s : ℂ).im = Real.sqrt 3 / 2 := by
    have h_prod : ((s : ℂ).im - Real.sqrt 3 / 2) *
        ((s : ℂ).im + Real.sqrt 3 / 2) = 0 := by
      nlinarith [Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos s.2 (by positivity)))
  apply UpperHalfPlane.ext; apply Complex.ext <;>
    simp only [ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk, add_re, add_im, one_re, one_im,
      div_ofNat_re, div_ofNat_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add, zero_div] <;>
    linarith

omit f hf in
private lemma unit_circle_re_zero_eq_i' (s : ℍ)
    (hs_norm : ‖(s : ℂ)‖ = 1) (hs_re : (s : ℂ).re = 0) : s = ellipticPointI' := by
  apply UpperHalfPlane.ext; change (s : ℂ) = (ellipticPointI' : ℂ)
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re, mul_zero, zero_add] at h_nsq
  have h_le : (s : ℂ).im ≤ 1 := by nlinarith [mul_self_nonneg ((s : ℂ).im - 1), h_nsq]
  have h_ge : 1 ≤ (s : ℂ).im := by
    nlinarith [mul_le_of_le_one_right s.2.le h_le, h_nsq]
  apply Complex.ext
  · exact hs_re.trans Complex.I_re.symm
  · exact (le_antisymm h_le h_ge).trans Complex.I_im.symm

/-! ### Elliptic three-point sum decomposition -/

/-- The sum of `g` over the elliptic points in `S` equals `g(i) + g(rho) + g(rho+1)`,
provided that `g p = 0` for any FD point not in `S`. -/
omit f hf in
private lemma elliptic_sum_eq_three (S : Finset UpperHalfPlane)
    (g : UpperHalfPlane → ℂ) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_zero : ∀ p, p ∈ 𝒟 → p ∉ S → g p = 0) :
    let P := fun (p : UpperHalfPlane) =>
      p = ellipticPointI' ∨ p = ellipticPointRho' ∨ p = ellipticPointRhoPlusOne'
    ∑ s ∈ S.filter P, g s =
      g ellipticPointI' + g ellipticPointRho' + g ellipticPointRhoPlusOne' := by
  intro P
  have h_ell_sub : S.filter P ⊆
      ({ellipticPointI', ellipticPointRho',
        ellipticPointRhoPlusOne'} : Finset UpperHalfPlane) := by
    intro x hx; have := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_insert, Finset.mem_singleton]; exact this
  have h_zero_outside : ∀ x ∈
      ({ellipticPointI', ellipticPointRho',
        ellipticPointRhoPlusOne'} : Finset UpperHalfPlane),
      x ∉ S.filter P → g x = 0 := by
    intro x hx hx_not
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hx_not_S : x ∉ S :=
      fun hx_S => hx_not (Finset.mem_filter.mpr ⟨hx_S, hx⟩)
    have hx_fd : x ∈ 𝒟 := by
      rcases hx with rfl | rfl | rfl
      · exact ellipticPointI_mem_fd
      · exact ellipticPointRho_mem_fd
      · exact ellipticPointRhoPlusOne_mem_fd
    exact hS_zero x hx_fd hx_not_S
  rw [Finset.sum_subset h_ell_sub h_zero_outside,
    Finset.sum_insert (by simp [ellipticPointI_ne_rho, ellipticPoint_ne_iρ1']),
    Finset.sum_insert (by simp [ellipticPoint_ne_ρρ1']), Finset.sum_singleton]
  ring

/-! ### Point classification for FD boundary -/

/-- A non-elliptic FD point that is not in the strict interior must lie on one of
the four boundary segments: right vert, left vert, right arc (non-elliptic),
left arc (non-elliptic). -/
omit f hf in
private lemma fd_point_classification (s : ℍ) (hs_fd : s ∈ 𝒟)
    (hsi : s ≠ ellipticPointI') (hsρ : s ≠ ellipticPointRho')
    (hsρ1 : s ≠ ellipticPointRhoPlusOne')
    (h_not_int : ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2)) :
    (‖(s : ℂ)‖ > 1 ∧ (s : ℂ).re = 1/2) ∨
    (‖(s : ℂ)‖ > 1 ∧ (s : ℂ).re = -1/2) ∨
    (‖(s : ℂ)‖ = 1 ∧ (s : ℂ).re > 0) ∨
    (‖(s : ℂ)‖ = 1 ∧ (s : ℂ).re < 0) := by
  have hnorm_ge : 1 ≤ ‖(s : ℂ)‖ := by
    rw [Complex.norm_def]; exact Real.sqrt_one ▸ Real.sqrt_le_sqrt hs_fd.1
  rcases eq_or_lt_of_le hnorm_ge with h_eq | h_gt
  · rcases lt_trichotomy (s : ℂ).re 0 with hre_neg | hre_zero | hre_pos
    · exact Or.inr (Or.inr (Or.inr ⟨h_eq.symm, hre_neg⟩))
    · exact absurd (unit_circle_re_zero_eq_i' s h_eq.symm hre_zero) hsi
    · exact Or.inr (Or.inr (Or.inl ⟨h_eq.symm, hre_pos⟩))
  · have h_abs_eq : |(s : ℂ).re| = 1/2 := by
      by_contra h_ne; exact h_not_int ⟨h_gt, lt_of_le_of_ne hs_fd.2 h_ne⟩
    rcases abs_cases (s : ℂ).re with ⟨h_eq_abs, _⟩ | ⟨h_eq_abs, _⟩
    · exact Or.inl ⟨h_gt, by linarith⟩
    · exact Or.inr (Or.inl ⟨h_gt, by linarith⟩)

/-! ### Stage 1: Winding sum equals explicit-coefficient form -/

/-- For a non-elliptic, non-interior FD point, the winding number from
`FDWindingDataFull` equals `-1/2`.

This bundles the necessary point classification to invoke `boundary_winding`. -/
private lemma gWN_boundary_eq_neg_half {H : ℝ}
    (wd : FDWindingDataFull H) (s : ℍ) (hs_fd : s ∈ 𝒟)
    (hs_below : (s : ℂ).im < H)
    (hsi : s ≠ ellipticPointI') (hsρ : s ≠ ellipticPointRho')
    (hsρ1 : s ≠ ellipticPointRhoPlusOne')
    (h_not_int : ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2)) :
    generalizedWindingNumber wd.boundary (↑s : ℂ) = -1/2 :=
  (wd.boundary_winding (↑s) s.2 hs_below
    (by intro h; exact hsi (UpperHalfPlane.ext h))
    (by intro h; exact hsρ (UpperHalfPlane.ext h))
    (by intro h; exact hsρ1 (UpperHalfPlane.ext h))
    h_not_int hs_fd.1 hs_fd.2).eq

/-- **Stage 1**: The winding-weighted sum over a zero set `S_0` can be rewritten
in explicit-coefficient form, using the known winding values from `FDWindingDataFull`.

This is the algebraic core: substitute known gWN values, apply orbit pairing, and
collect terms. The proof mirrors `valence_formula_core_of_windingDataFull` but runs
in the "forward" direction (computing what the winding sum equals).

Specifically:
```
sum_{s in S_0} (-gWN(s)) * ord(s)
  = (1/2)*ord(i) + (1/3)*ord(rho)
    + sum_strict_int ord + sum_left_vert ord + sum_left_arc ord
```
-/
include hf in
private theorem winding_sum_eq_explicit {H : ℝ}
    (wd : FDWindingDataFull H)
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hS_below : ∀ s ∈ S, (s : ℂ).im < H) :
    ∑ s ∈ S, (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
      ↑(orderOfVanishingAt' (⇑f) s) =
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) := by
  -- Extract winding number values at the three elliptic points
  have hgw_i : generalizedWindingNumber wd.boundary I = -1/2 :=
    wd.winding_at_i.eq
  have hgw_ρ : generalizedWindingNumber wd.boundary ellipticPointRho = -1/6 :=
    wd.winding_at_rho.eq
  have hgw_ρ1 : generalizedWindingNumber wd.boundary ellipticPointRhoPlusOne = -1/6 :=
    wd.winding_at_rho_plus_one.eq
  -- Interior winding = -1
  have hgw_int : ∀ s ∈ S, ‖(s : ℂ)‖ > 1 → |(s : ℂ).re| < 1/2 →
      generalizedWindingNumber wd.boundary (↑s) = -1 := fun s hs hn hr =>
    (wd.interior_winding (↑s) hn hr s.2 (hS_below s hs)).eq
  -- Boundary winding = -1/2
  have hgw_bdry : ∀ s ∈ S, s ≠ ellipticPointI' → s ≠ ellipticPointRho' →
      s ≠ ellipticPointRhoPlusOne' → ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) →
      generalizedWindingNumber wd.boundary (↑s) = -1/2 := by
    intro s hs hsi hsρ hsρ1 h_not_int
    exact gWN_boundary_eq_neg_half wd s (hS s hs) (hS_below s hs) hsi hsρ hsρ1 h_not_int
  -- Set up the negated-winding function
  set g := fun (s : UpperHalfPlane) =>
    (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
      (orderOfVanishingAt' (⇑f) s : ℂ) with hg_def
  have h_ord_zero : ∀ p, p ∈ 𝒟 → p ∉ S → orderOfVanishingAt' (⇑f) p = 0 :=
    fun p hp hp_not => by_contra fun h_ne => hp_not (hS_complete _ hp h_ne)
  -- Split into elliptic + non-elliptic
  set P := fun (p : UpperHalfPlane) =>
    p = ellipticPointI' ∨ p = ellipticPointRho' ∨ p = ellipticPointRhoPlusOne'
  have h_split : ∑ s ∈ S, g s =
      ∑ s ∈ S.filter P, g s + ∑ s ∈ S.filter (fun p => ¬P p), g s :=
    (Finset.sum_filter_add_sum_filter_not S P g).symm
  have h_ell_sum : ∑ s ∈ S.filter P, g s =
      g ellipticPointI' + g ellipticPointRho' + g ellipticPointRhoPlusOne' :=
    elliptic_sum_eq_three S g hS (fun p hp hp_not => by
      simp [hg_def, h_ord_zero p hp hp_not, Int.cast_zero, mul_zero])
  -- Evaluate g at elliptic points
  have hg_i : g ellipticPointI' =
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') := by
    show (-generalizedWindingNumber wd.boundary I) *
      ↑(orderOfVanishingAt' (⇑f) ellipticPointI') = _; rw [hgw_i]; ring
  have hg_ρ : g ellipticPointRho' =
      (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') := by
    show (-generalizedWindingNumber wd.boundary ellipticPointRho) *
      ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') = _; rw [hgw_ρ]; ring
  have hg_ρ1 : g ellipticPointRhoPlusOne' =
      (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne') := by
    show (-generalizedWindingNumber wd.boundary ellipticPointRhoPlusOne) *
      ↑(orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne') = _; rw [hgw_ρ1]; ring
  -- Combine rho and rho+1 using T-invariance: ord(rho+1) = ord(rho)
  rw [ord_rho_plus_one_eq_ord_rho_via_vAdd f] at hg_ρ1
  -- Non-elliptic filter
  have h_filter_eq : S.filter (fun p => ¬P p) = S.filter (fun p =>
      p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne') := by
    ext x; simp only [P, Finset.mem_filter, not_or]
  set S_NE := S.filter (fun p =>
    p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧
    p ≠ ellipticPointRhoPlusOne') with hS_NE_def
  set INT := S.filter (fun p =>
    p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
    ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)
  -- Each non-elliptic point: interior → coefficient 1, boundary → coefficient 1/2
  have h_gWN_val : ∀ s ∈ S_NE, g s =
      (if ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2 then (1 : ℂ) else 1/2) *
        ↑(orderOfVanishingAt' (⇑f) s) := by
    intro s hs
    simp only [hS_NE_def, Finset.mem_filter] at hs
    obtain ⟨hs_S, hsi, hsρ, hsρ1⟩ := hs
    split_ifs with h_int
    · simp only [hg_def]; rw [hgw_int s hs_S h_int.1 h_int.2]; ring
    · simp only [hg_def]; rw [hgw_bdry s hs_S hsi hsρ hsρ1 h_int]; ring
  -- Rewrite the non-elliptic sum using the known values
  have h_ne_sum : ∑ s ∈ S.filter (fun p => ¬P p), g s =
      ∑ s ∈ S_NE, g s := by rw [h_filter_eq]
  rw [h_split, h_ell_sum, hg_i, hg_ρ, hg_ρ1, h_ne_sum,
    Finset.sum_congr rfl h_gWN_val]
  -- Split non-elliptic into interior + boundary
  have h_ne_int : S_NE.filter
      (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2) = INT := by
    ext s; simp only [hS_NE_def, INT, Finset.mem_filter]; tauto
  set BDRY := S_NE.filter
    (fun (p : ℍ) => ¬(‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2))
  have h_split2 := Finset.sum_filter_add_sum_filter_not S_NE
    (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2) (fun s =>
      (if ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
        ↑(orderOfVanishingAt' (⇑f) s))
  have h_int_sum :
      ∑ x ∈ S_NE.filter (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
        (if ‖(x : ℂ)‖ > 1 ∧ |(x : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
          ↑(orderOfVanishingAt' (⇑f) x) =
      ∑ x ∈ INT, ↑(orderOfVanishingAt' (⇑f) x) := by
    rw [h_ne_int]; apply Finset.sum_congr rfl; intro s hs
    simp only [INT, Finset.mem_filter] at hs
    rw [if_pos ⟨hs.2.2.2.2.1, hs.2.2.2.2.2⟩, one_mul]
  have h_bdry_sum :
      ∑ x ∈ BDRY,
        (if ‖(x : ℂ)‖ > 1 ∧ |(x : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
          ↑(orderOfVanishingAt' (⇑f) x) =
      (1/2 : ℂ) * ∑ x ∈ BDRY, (orderOfVanishingAt' (⇑f) x : ℂ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s hs
    rw [if_neg (show ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) from
      (Finset.mem_filter.mp hs).2)]
  -- Half the boundary sum = left vert + left arc (orbit pairing)
  set LA_ne := S.filter (fun p =>
    p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)
  -- We need: (1/2) * Σ_BDRY ord = Σ_leftVert ord + Σ_leftArc ord
  -- This follows from the orbit pairing: right vert ↔ left vert, right arc ↔ left arc
  -- First establish the BDRY decomposition into 4 disjoint parts
  set RA_ne := S.filter (fun p =>
    p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0) with hRA_ne_def
  -- BDRY = right vert ∪ left vert ∪ RA_ne ∪ LA_ne
  have h_bdry_decomp : BDRY =
      (sRightVert S) ∪ (sLeftVert S) ∪ RA_ne ∪ LA_ne := by
    ext s
    simp only [BDRY, S_NE, hS_NE_def, sRightVert, sLeftVert, RA_ne, hRA_ne_def, LA_ne,
      Finset.mem_union, Finset.mem_filter]
    have h_rho_norm := ellipticPointRho_norm
    have h_rho1_norm := ellipticPointRhoPlusOne_norm
    constructor
    · intro ⟨⟨hs_S, hsi, hsρ, hsρ1⟩, h_not_int⟩
      have hs_fd := hS s hs_S
      have hnorm_ge : 1 ≤ ‖(s : ℂ)‖ := by
        rw [Complex.norm_def]; exact Real.sqrt_one ▸ Real.sqrt_le_sqrt hs_fd.1
      rcases eq_or_lt_of_le hnorm_ge with h_eq | h_gt
      · rcases lt_trichotomy (s : ℂ).re 0 with hre_neg | hre_zero | hre_pos
        · exact Or.inr ⟨hs_S, hsρ, h_eq.symm, hre_neg⟩
        · exact absurd (unit_circle_re_zero_eq_i' s h_eq.symm hre_zero) hsi
        · exact Or.inl (Or.inr (Or.inl ⟨hs_S, hsρ1, h_eq.symm, hre_pos⟩))
      · have h_abs_eq : |(s : ℂ).re| = 1/2 := by
          by_contra h_ne; exact h_not_int ⟨h_gt, lt_of_le_of_ne hs_fd.2 h_ne⟩
        rcases abs_cases (s : ℂ).re with ⟨_, h_sign⟩ | ⟨_, h_sign⟩
        · exact Or.inl (Or.inl (Or.inl ⟨hs_S, by linarith, h_gt⟩))
        · exact Or.inl (Or.inl (Or.inr ⟨hs_S, by linarith, h_gt⟩))
    · intro h
      rcases h with ((⟨hs, hre, hn⟩ | ⟨hs, hre, hn⟩) | ⟨hs, hne, hn_eq, hre⟩) |
        ⟨hs, hne, hn_eq, hre⟩
      · exact ⟨⟨hs,
          fun h => by rw [h] at hre; norm_num [ellipticPointI'] at hre,
          fun h => by rw [h] at hn; linarith [h_rho_norm],
          fun h => by rw [h] at hn; linarith [h_rho1_norm]⟩,
          fun ⟨_, h⟩ => by have := (abs_lt.mp h).2; linarith⟩
      · exact ⟨⟨hs,
          fun h => by rw [h] at hre; norm_num [ellipticPointI'] at hre,
          fun h => by rw [h] at hn; linarith [h_rho_norm],
          fun h => by rw [h] at hn; linarith [h_rho1_norm]⟩,
          fun ⟨_, h⟩ => by have := (abs_lt.mp h).1; linarith⟩
      · exact ⟨⟨hs,
          fun h => by rw [h] at hre; simp [ellipticPointI'] at hre,
          fun h => by rw [h] at hre; linarith [ellipticPointRho_re_neg'],
          hne⟩,
          fun ⟨h, _⟩ => by linarith⟩
      · exact ⟨⟨hs,
          fun h => by rw [h] at hre; simp [ellipticPointI'] at hre,
          hne,
          fun h => by rw [h] at hre; linarith [ellipticPointRhoPlusOne_re_pos']⟩,
          fun ⟨h, _⟩ => by linarith⟩
  -- Disjointness of the 4 parts
  have h_disj_RV_LV : Disjoint (sRightVert S) (sLeftVert S) :=
    Finset.disjoint_filter.mpr fun s _ ⟨hre1, _⟩ ⟨hre2, _⟩ => by linarith
  have h_disj_12 : Disjoint (sRightVert S ∪ sLeftVert S) RA_ne :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_filter.mpr fun s _ ⟨_, hn⟩ ⟨_, hn_eq, _⟩ => by linarith,
        Finset.disjoint_filter.mpr fun s _ ⟨hre, _⟩ ⟨_, _, hre2⟩ => by linarith⟩
  have h_disj_3 : Disjoint (sRightVert S ∪ sLeftVert S ∪ RA_ne) LA_ne :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_filter.mpr
            fun s _ ⟨hre, _⟩ ⟨_, _, hre2⟩ => by linarith,
          Finset.disjoint_filter.mpr
            fun s _ ⟨_, hn⟩ ⟨_, hn_eq, _⟩ => by linarith⟩,
        Finset.disjoint_filter.mpr
          fun s _ ⟨_, _, hre1⟩ ⟨_, _, hre2⟩ => by linarith⟩
  -- Decompose the BDRY sum
  have h_bdry_sum_decomp :
      ∑ s ∈ BDRY, (orderOfVanishingAt' (⇑f) s : ℂ) =
      ∑ s ∈ sRightVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ sLeftVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ RA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ LA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) := by
    rw [h_bdry_decomp,
      Finset.sum_union h_disj_3,
      Finset.sum_union h_disj_12,
      Finset.sum_union h_disj_RV_LV]
  -- Use orbit pairing: right vert ↔ left vert
  have h_rv_lv := sum_ord_rightVert_eq_sum_ord_leftVert f S hS hS_complete
  -- Use orbit pairing: right arc ↔ left arc
  have h_ra_la := sum_ord_rightArc_eq_sum_ord_leftArc f S hS hS_complete
  -- Decompose right/left arc sums into elliptic + non-elliptic
  have h_ra_eq : RA_ne = (sRightArc S).filter (· ≠ ellipticPointRhoPlusOne') := by
    ext s; simp only [RA_ne, hRA_ne_def, sRightArc, Finset.mem_filter]; tauto
  have h_la_eq : LA_ne = (sLeftArc S).filter (· ≠ ellipticPointRho') := by
    ext s; simp only [LA_ne, sLeftArc, Finset.mem_filter]; tauto
  -- Split arc sums into elliptic singleton + non-elliptic
  set f_ord := fun s : ℍ => (orderOfVanishingAt' (⇑f) s : ℂ) with hf_ord_def
  have h_ra_split := Finset.sum_filter_add_sum_filter_not (sRightArc S)
    (· ≠ ellipticPointRhoPlusOne') f_ord
  have h_la_split := Finset.sum_filter_add_sum_filter_not (sLeftArc S)
    (· ≠ ellipticPointRho') f_ord
  -- The elliptic singletons from right/left arcs
  have h_sing :
      ∑ p ∈ (sRightArc S).filter
          (fun x => ¬(x ≠ ellipticPointRhoPlusOne')), f_ord p =
      ∑ p ∈ (sLeftArc S).filter
          (fun x => ¬(x ≠ ellipticPointRho')), f_ord p := by
    simp_rw [not_not]
    conv_lhs => rw [Finset.filter_eq' (sRightArc S) ellipticPointRhoPlusOne']
    conv_rhs => rw [Finset.filter_eq' (sLeftArc S) ellipticPointRho']
    by_cases h_ord : orderOfVanishingAt' (⇑f) ellipticPointRho' = 0
    · have hf1 : f_ord ellipticPointRho' = 0 := by simp [hf_ord_def, h_ord]
      have hf2 : f_ord ellipticPointRhoPlusOne' = 0 := by
        simp [hf_ord_def, ord_rho_plus_one_eq_ord_rho_via_vAdd f ▸ h_ord]
      split_ifs <;> simp [Finset.sum_singleton, Finset.sum_empty, hf1, hf2]
    · have hρ_in_LA : ellipticPointRho' ∈ sLeftArc S := by
        simp only [sLeftArc, Finset.mem_filter]
        exact ⟨hS_complete _ ellipticPointRho_mem_fd h_ord,
          ellipticPointRho_norm, ellipticPointRho_re_neg'⟩
      have hρ1_in_RA : ellipticPointRhoPlusOne' ∈ sRightArc S := by
        simp only [sRightArc, Finset.mem_filter]
        exact ⟨hS_complete _ ellipticPointRhoPlusOne_mem_fd
          (by rwa [ord_rho_plus_one_eq_ord_rho_via_vAdd]),
          ellipticPointRhoPlusOne_norm, ellipticPointRhoPlusOne_re_pos'⟩
      rw [if_pos hρ1_in_RA, if_pos hρ_in_LA, Finset.sum_singleton, Finset.sum_singleton]
      exact_mod_cast congr_arg (Int.cast (R := ℂ)) (ord_rho_plus_one_eq_ord_rho_via_vAdd f)
  -- Non-elliptic arc pairing: RA_ne sum = LA_ne sum
  have h_ra_ne_la_ne :
      ∑ p ∈ RA_ne, f_ord p = ∑ p ∈ LA_ne, f_ord p := by
    rw [h_ra_eq, h_la_eq]
    linear_combination
      h_ra_la + h_ra_split - h_la_split - h_sing
  -- Now assemble: (1/2) * BDRY sum = left vert + left arc
  have h_half_bdry :
      (1/2 : ℂ) * ∑ s ∈ BDRY, (orderOfVanishingAt' (⇑f) s : ℂ) =
      ∑ s ∈ sLeftVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ LA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) := by
    rw [h_bdry_sum_decomp, h_rv_lv, h_ra_ne_la_ne]; ring
  -- Final assembly
  linear_combination h_int_sum + h_bdry_sum + h_half_bdry - h_split2

/-! ### Stage 2: The winding-form identity -/

include hf in
/-- **The core identity proof**: the winding-form identity for any zero set `S_0`.

This combines Stage 1 (`winding_sum_eq_explicit`) with `valence_formula_orbit_sum`
from `CoreIdentity.lean` to produce the winding-form identity needed by
`ResidueModularData.h_identity_for_zeros`. -/
theorem coreIdentityProof {H : ℝ}
    (wd : FDWindingDataFull H)
    (S₀ : Finset UpperHalfPlane) (hS₀ : ∀ p ∈ S₀, p ∈ 𝒟)
    (hS₀_nonzero : ∀ s ∈ S₀, orderOfVanishingAt' (⇑f) s ≠ 0)
    (hS₀_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S₀)
    (hS₀_below : ∀ s ∈ S₀, (s : ℂ).im < H) :
    (orderAtCusp' f : ℂ) +
    ∑ s ∈ S₀, (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
      ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12 := by
  -- Stage 1: rewrite the winding sum as the explicit-coefficient form
  have h_sum_eq := winding_sum_eq_explicit f hf wd S₀ hS₀ hS₀_complete hS₀_below
  rw [h_sum_eq]
  -- Stage 2: the explicit-coefficient form equals k/12
  exact valence_formula_orbit_sum f hf S₀ hS₀ hS₀_complete

/-! ### Construction of unconditional ResidueModularData -/

include hf in
/-- Construct `ResidueModularData` unconditionally from `FDWindingDataFull` and a
height bound on zeros.

The `h_identity_for_zeros` field is filled by `coreIdentityProof`, which combines
the known winding values from `FDWindingDataFull` with the orbit-sum formula from
`CoreIdentity.lean`. No additional hypotheses are needed. -/
def mk_residueModularData_unconditional {H : ℝ} (hH : 1 < H)
    (wd : FDWindingDataFull H)
    (h_above : ∀ p : ℍ, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → (p : ℂ).im < H) :
    ResidueModularData f where
  H := H
  hH := hH
  wd := wd
  h_above_zeros := h_above
  h_identity_for_zeros := fun S₀ hS₀ hS₀_nonzero hS₀_complete =>
    coreIdentityProof f hf wd S₀ hS₀ hS₀_nonzero hS₀_complete
      (fun s hs => h_above s (hS₀ s hs) (hS₀_nonzero s hs))

/-! ### The unconditional valence formula -/

include hf in
/-- **The Valence Formula** -- unconditional modulo `FDWindingDataFull` and height bound.

Given `FDWindingDataFull H` (the five winding number witnesses) and a height above
all FD zeros, this produces the textbook valence formula with no further hypotheses.

This discharges the last remaining gap (`h_identity_for_zeros`) in the chain:
`FDWindingDataFull` + `h_above_zeros` --> `ResidueModularData` --> textbook formula. -/
theorem valence_formula_unconditional {H : ℝ} (hH : 1 < H)
    (wd : FDWindingDataFull H)
    (h_above : ∀ p : ℍ, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → (p : ℂ).im < H) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 :=
  valence_formula_from_residueModularData f hf
    (mk_residueModularData_unconditional f hf hH wd h_above)

end
