/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.Modularforms.PeterssonInner
import LeanModularForms.Modularforms.PSL2Action
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Coset.Basic

/-!
# Level-N Petersson Inner Product

The **level-N Petersson inner product** on `S_k(Γ₁(N))`, defined as a sum over
left coset representatives of `Γ₁(N)` in `SL₂(ℤ)`:

$$\langle f, g \rangle_N = \sum_{[\delta] \in \mathrm{SL}_2(\mathbb{Z})\,/\,\Gamma_1(N)}
  \int_{\mathcal{D}} \overline{(f|\delta^{-1})(\tau)}\,(g|\delta^{-1})(\tau)\,
  (\mathrm{Im}\,\tau)^k\,d\mu(\tau)$$

This equals `∫_{D_N} petersson k f g dμ` where `D_N = ⋃_δ δ⁻¹(𝒟)` is a
`Γ₁(N)`-fundamental domain.

## Main definitions

* `petN`: the level-N Petersson inner product (un-normalized).

## Main results

* `petN_conj_symm`: Hermitian symmetry `conj(petN g f) = petN f g`.
* `petN_definite`: positive-definiteness `petN f f = 0 → f = 0`.
* `slash_Gamma1_eq`: for `γ ∈ Γ₁(N)`, `f∣γ = f`.

The inner product is deliberately not normalized by `1/V_Γ`; a positive-definite
Hermitian form suffices downstream.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.4
* [Miy] Miyake, *Modular Forms*, §2.5
-/

noncomputable section

open scoped MatrixGroups ModularForm Pointwise
open UpperHalfPlane ModularGroup CongruenceSubgroup MeasureTheory Matrix.SpecialLinearGroup

variable {N : ℕ} [NeZero N] {k : ℤ}

instance : Fintype (SL(2, ℤ) ⧸ Gamma1 N) := Subgroup.fintypeQuotientOfFiniteIndex

/-! ### Slash invariance under Γ₁(N) -/

/-- For `γ ∈ Γ₁(N)`, the weight-`k` slash action on a `Γ₁(N)`-cusp form is trivial. -/
theorem slash_Gamma1_eq
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    ⇑f ∣[k] γ = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩

/-! ### Level-N Petersson inner product -/

/-- The level-N Petersson inner product on `S_k(Γ₁(N))`, defined as
`petN f g = Σ_{[δ] ∈ SL₂(ℤ)/Γ₁(N)} ∫_fd petersson k (f∣δ⁻¹) (g∣δ⁻¹) dμ`. -/
def petN (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : ℂ :=
  ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
    peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹)

/-! ### Algebraic properties -/

/-- Hermitian symmetry: `conj(petN g f) = petN f g`. -/
theorem petN_conj_symm
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    starRingEnd ℂ (petN g f) = petN f g := by
  simp only [petN, map_sum, peterssonInner_conj_symm]

/-- `petN f 0 = 0`. -/
theorem petN_zero_right
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f 0 = 0 := by
  simp [petN, peterssonInner_zero_right]

/-- `petN 0 g = 0`. -/
theorem petN_zero_left
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN 0 g = 0 := by
  simp [petN, peterssonInner_zero_left]

/-! ### Integrability of slashed petersson integrand -/

/-- The Petersson integrand of slashed cusp forms is integrable on `fd`. -/
theorem integrableOn_petersson_slash
    {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    [CuspFormClass F Γ k] [ModularFormClass F' Γ k]
    (f : F) (f' : F') (δ : SL(2, ℤ)) :
    IntegrableOn (fun τ ↦ petersson k (⇑f ∣[k] δ) (⇑f' ∣[k] δ) τ) fd μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ f f'
  rw [show (fun τ ↦ petersson k (⇑f ∣[k] δ) (⇑f' ∣[k] δ) τ) =
      fun τ ↦ petersson k (⇑f) (⇑f') (δ • τ) from
    funext fun τ ↦ petersson_slash_SL k _ _ δ τ]
  exact IntegrableOn.of_bound hyperbolicMeasure_fd_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f')).comp (continuous_const_smul δ)
    |>.aestronglyMeasurable.restrict)
    C (ae_of_all _ fun τ ↦ hC (δ • τ))

/-! ### Positive definiteness -/

private theorem out_one_mem_Gamma1 :
    ((⟦1⟧ : SL(2, ℤ) ⧸ Gamma1 N)).out ∈ Gamma1 N := by
  have h := Quotient.exact ((⟦1⟧ : SL(2, ℤ) ⧸ Gamma1 N).out_eq)
  change (QuotientGroup.leftRel (Gamma1 N)).r _ _ at h
  rw [QuotientGroup.leftRel_apply] at h; simpa using h

private theorem identity_coset_eq_pet
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k fd
      (⇑f ∣[k] (⟦(1 : SL(2, ℤ))⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹)
      (⇑g ∣[k] (⟦(1 : SL(2, ℤ))⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹) =
    CuspForm.pet f g := by
  have hmem := (Gamma1 N).inv_mem out_one_mem_Gamma1
  simp only [slash_Gamma1_eq f _ hmem, slash_Gamma1_eq g _ hmem, CuspForm.pet, peterssonInner]

private theorem petersson_self_ofReal (h : ℍ → ℂ) (τ : ℍ) :
    petersson k h h τ = ↑(Complex.normSq (h τ) * τ.im ^ k) := by
  simp only [petersson]
  rw [show (starRingEnd ℂ) (h τ) * h τ = ↑(Complex.normSq (h τ)) from
    Complex.normSq_eq_conj_mul_self.symm]
  push_cast; ring

private theorem peterssonInner_self_real (h : ℍ → ℂ) :
    peterssonInner k fd h h =
      ↑(∫ τ in fd, Complex.normSq (h τ) * τ.im ^ k ∂hyperbolicMeasure) := by
  show ∫ τ in fd, petersson k h h τ ∂hyperbolicMeasure = _
  simp_rw [petersson_self_ofReal]
  exact integral_ofReal

private theorem measurableSet_fd' : MeasurableSet (fd : Set ℍ) :=
  ((isClosed_le continuous_const (Complex.continuous_normSq.comp continuous_coe)).inter
    (isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re)
      continuous_const)).measurableSet

/-- Each summand of `petN f f` is a non-negative real number. -/
theorem petN_summand_nonneg
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ∃ r : ℝ, 0 ≤ r ∧
      peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑f ∣[k] (q.out)⁻¹) = ↑r := by
  set h := ⇑f ∣[k] (q.out)⁻¹
  refine ⟨∫ τ in fd, Complex.normSq (h τ) * τ.im ^ k ∂hyperbolicMeasure,
    setIntegral_nonneg measurableSet_fd' fun τ _ ↦
      mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos τ).le _),
    peterssonInner_self_real h⟩

/-- **Positive definiteness** of the level-N Petersson inner product. -/
theorem petN_definite
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hpet : petN f f = 0) : f = 0 := by
  apply CuspForm.pet_definite f
  rw [← identity_coset_eq_pet f f]
  choose r hr_nonneg hr_eq using petN_summand_nonneg f
  have hsum : (↑(∑ q, r q) : ℂ) = 0 := by
    rw [Complex.ofReal_sum]; simp_rw [← hr_eq]; exact hpet
  have hzero : ∀ q, r q = 0 := fun q ↦
    (Finset.sum_eq_zero_iff_of_nonneg fun q _ ↦ hr_nonneg q).mp
      (Complex.ofReal_eq_zero.mp hsum) q (Finset.mem_univ q)
  rw [hr_eq ⟦1⟧, hzero ⟦1⟧, Complex.ofReal_zero]

/-! ### Sesquilinearity -/

/-- Negation in the second argument. -/
theorem petN_neg_right
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (-g) = -petN f g := by
  simp only [petN, CuspForm.coe_neg, SlashAction.neg_slash, peterssonInner_neg_right,
    Finset.sum_neg_distrib]

/-- Negation in the first argument. -/
theorem petN_neg_left
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (-f) g = -petN f g := by
  simp only [petN, CuspForm.coe_neg, SlashAction.neg_slash, peterssonInner_neg_left,
    Finset.sum_neg_distrib]

/-- Additivity in the second argument. -/
theorem petN_add_right
    (f g₁ g₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (g₁ + g₂) = petN f g₁ + petN f g₂ := by
  simp only [petN]; rw [← Finset.sum_add_distrib]; congr 1; ext q
  have : ⇑(g₁ + g₂) ∣[k] (q.out)⁻¹ =
      (⇑g₁ ∣[k] (q.out)⁻¹) + (⇑g₂ ∣[k] (q.out)⁻¹) := by
    rw [CuspForm.coe_add]; exact SlashAction.add_slash k _ _ _
  rw [this]
  exact peterssonInner_add_right k fd _ _ _
    (integrableOn_petersson_slash f g₁ (q.out)⁻¹)
    (integrableOn_petersson_slash f g₂ (q.out)⁻¹)

private lemma smul_slash_SL (c : ℂ) (f : ℍ → ℂ) (δ : SL(2, ℤ)) :
    (c • f) ∣[k] δ = c • (f ∣[k] δ) := by
  rw [ModularForm.SL_slash (c • f) δ, ModularForm.SL_slash f δ, ModularForm.smul_slash]
  simp [UpperHalfPlane.σ, Matrix.SpecialLinearGroup.map]

/-- Complex scalar in the second argument: `petN f (c • g) = c * petN f g`. -/
theorem petN_smul_right (c : ℂ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (c • g) = c * petN f g := by
  simp only [petN]
  simp_rw [show ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k fd (⇑f ∣[k] q.out⁻¹) (⇑(c • g) ∣[k] q.out⁻¹) =
      c * peterssonInner k fd (⇑f ∣[k] q.out⁻¹) (⇑g ∣[k] q.out⁻¹) from fun q ↦ by
    rw [show ⇑(c • g) ∣[k] q.out⁻¹ = c • (⇑g ∣[k] q.out⁻¹) from by
      change (c • ⇑g) ∣[k] q.out⁻¹ = c • (⇑g ∣[k] q.out⁻¹)
      exact smul_slash_SL c _ _]
    exact peterssonInner_smul_right k _ c _ _]
  exact (Finset.mul_sum _ _ _).symm

/-- Conjugate-complex scalar in the first argument:
`petN (c • f) g = conj(c) * petN f g`. -/
theorem petN_conj_smul_left (c : ℂ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (c • f) g = starRingEnd ℂ c * petN f g :=
  calc petN (c • f) g
      = starRingEnd ℂ (petN g (c • f)) := (petN_conj_symm _ _).symm
    _ = starRingEnd ℂ (c * petN g f) := by rw [petN_smul_right]
    _ = starRingEnd ℂ c * starRingEnd ℂ (petN g f) := map_mul _ _ _
    _ = starRingEnd ℂ c * petN f g := by rw [petN_conj_symm]

/-- Additivity in the first argument. -/
theorem petN_add_left
    (f₁ f₂ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (f₁ + f₂) g = petN f₁ g + petN f₂ g :=
  calc petN (f₁ + f₂) g
      = starRingEnd ℂ (petN g (f₁ + f₂)) := (petN_conj_symm _ _).symm
    _ = starRingEnd ℂ (petN g f₁ + petN g f₂) := by rw [petN_add_right]
    _ = starRingEnd ℂ (petN g f₁) + starRingEnd ℂ (petN g f₂) := map_add _ _ _
    _ = petN f₁ g + petN f₂ g := by rw [petN_conj_symm, petN_conj_symm]

/-! ### Γ₁(N)-fundamental domain infrastructure -/

namespace MeasureTheory

private theorem eq_of_mul_out_inv_eq {G : Type*} [Group G] {H : Subgroup G}
    {r₁ r₂ : G ⧸ H} {a b : H}
    (hh : (a : G) * (r₁.out)⁻¹ = (b : G) * (r₂.out)⁻¹) : a = b := by
  have hmem : (r₂.out : G)⁻¹ * r₁.out ∈ H := by
    have he : (b : G)⁻¹ * (a : G) = (r₂.out : G)⁻¹ * (r₁.out : G) := by
      have h2 : (b : G)⁻¹ * ((a : G) * (r₁.out)⁻¹) * r₁.out
          = (b : G)⁻¹ * ((b : G) * (r₂.out)⁻¹) * r₁.out := by rw [hh]
      simpa [mul_assoc] using h2
    rw [← he]; exact H.mul_mem (H.inv_mem b.2) a.2
  have hq : r₁ = r₂ := by
    have h_mk : (QuotientGroup.mk r₁.out : G ⧸ H) = QuotientGroup.mk r₂.out := by
      rw [QuotientGroup.eq]; simpa [mul_inv_rev] using H.inv_mem hmem
    simpa using h_mk
  subst hq
  exact Subtype.ext (mul_right_cancel hh)

/-- **Subgroup coset tiling of a fundamental domain.** If `s` is a fundamental
domain for a group `G` acting on `α`, then for any subgroup `H ≤ G`, the union of
`[G : H]`-many translates `(q.out)⁻¹ • s` (for `q ∈ G ⧸ H`) is a fundamental
domain for the restricted `H`-action on `α`. -/
theorem IsFundamentalDomain.subgroup_iUnion_out_smul
    {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]
    [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
    (H : Subgroup G) [Countable (G ⧸ H)] {s : Set α}
    (hs : IsFundamentalDomain G s μ) :
    IsFundamentalDomain H (⋃ q : G ⧸ H, ((q.out : G))⁻¹ • s) μ := by
  set T : Set α := ⋃ q : G ⧸ H, ((q.out : G))⁻¹ • s with hT_def
  refine ⟨.iUnion fun q ↦ hs.nullMeasurableSet_smul _, ?_, ?_⟩
  · filter_upwards [hs.ae_covers] with τ hτ
    obtain ⟨g, hg⟩ := hτ
    set q : G ⧸ H := QuotientGroup.mk g
    have hmem : q.out⁻¹ * g ∈ H := by
      rw [← QuotientGroup.leftRel_apply]
      exact Quotient.exact q.out_eq
    refine ⟨⟨q.out⁻¹ * g, hmem⟩, ?_⟩
    show (q.out⁻¹ * g) • τ ∈ T
    rw [mul_smul]
    refine Set.mem_iUnion.mpr ⟨q, ?_⟩
    exact Set.smul_mem_smul_set hg
  · intro h₁ h₂ hne
    show AEDisjoint μ ((h₁ : G) • T) ((h₂ : G) • T)
    rw [hT_def]
    simp only [Set.smul_set_iUnion]
    rw [AEDisjoint.iUnion_left_iff]
    intro q₁
    rw [AEDisjoint.iUnion_right_iff]
    intro q₂
    rw [show ((h₁ : G) • ((q₁.out : G))⁻¹ • s : Set α) =
          (((h₁ : G) * (q₁.out : G)⁻¹) • s : Set α) from (mul_smul _ _ _).symm,
        show ((h₂ : G) • ((q₂.out : G))⁻¹ • s : Set α) =
          (((h₂ : G) * (q₂.out : G)⁻¹) • s : Set α) from (mul_smul _ _ _).symm]
    exact hs.aedisjoint fun heq ↦ hne (eq_of_mul_out_inv_eq heq)

/-- **Normalizer-shift of a fundamental domain.** If `s` is an `H`-fundamental
domain (where `H ≤ G_outer`) and `g ∈ G_outer` lies in the normalizer of `H`,
then `g • s` is again an `H`-fundamental domain. -/
theorem IsFundamentalDomain.smul_of_mem_normalizer
    {G_outer α : Type*} [Group G_outer] [MeasurableSpace α] [MulAction G_outer α]
    [MeasurableConstSMul G_outer α] {μ : Measure α} [SMulInvariantMeasure G_outer α μ]
    {H : Subgroup G_outer} {s : Set α}
    (hs : IsFundamentalDomain H s μ) {g : G_outer} (hg : g ∈ H.normalizer) :
    IsFundamentalDomain H (g • s) μ :=
  hs.image_of_equiv (MulAction.toPerm g)
    (measurePreserving_smul _ _).quasiMeasurePreserving
    { toFun := fun h' ↦ ⟨g⁻¹ * (h' : G_outer) * g,
        (Subgroup.mem_normalizer_iff''.mp hg _).mp h'.2⟩
      invFun := fun h' ↦ ⟨g * (h' : G_outer) * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hg _).mp h'.2⟩
      left_inv := fun _ ↦ Subtype.ext (by group)
      right_inv := fun _ ↦ Subtype.ext (by group) }
    fun h' x ↦ by
      show g • ((g⁻¹ * (h' : G_outer) * g) • x) = (h' : G_outer) • (g • x)
      simp only [smul_smul, mul_inv_cancel_left, mul_assoc]

/-- **Conjugation-shift of a fundamental domain.** If `s` is an `H₁`-fundamental
domain (where `H₁ ≤ G_outer`) and `H₂` is the pointwise conjugate `g · H₁ · g⁻¹`
(in `Subgroup` pointwise smul form, via the `ConjAct G_outer`-action), then
`g • s` is an `H₂`-fundamental domain. -/
theorem IsFundamentalDomain.smul_of_eq_conjAct
    {G_outer α : Type*} [Group G_outer] [MeasurableSpace α] [MulAction G_outer α]
    [MeasurableConstSMul G_outer α] {μ : Measure α} [SMulInvariantMeasure G_outer α μ]
    {H₁ H₂ : Subgroup G_outer} {s : Set α} (hs : IsFundamentalDomain H₁ s μ)
    {g : G_outer} (hgH : H₂ = ConjAct.toConjAct g • H₁) :
    IsFundamentalDomain H₂ (g • s) μ := by
  subst hgH
  exact hs.image_of_equiv (MulAction.toPerm g)
    (measurePreserving_smul _ _).quasiMeasurePreserving
    { toFun := fun h₂ ↦ ⟨g⁻¹ * (h₂ : G_outer) * g, by
        have h_mem : (h₂ : G_outer) ∈ ConjAct.toConjAct g • H₁ := h₂.2
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
          ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h_mem
        exact h_mem⟩
      invFun := fun h₁ ↦ ⟨g * (h₁ : G_outer) * g⁻¹, by
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
          ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
        have h_simp : g⁻¹ * (g * (h₁ : G_outer) * g⁻¹) * g = (h₁ : G_outer) := by
          group
        rw [h_simp]
        exact h₁.2⟩
      left_inv := fun _ ↦ Subtype.ext (by group)
      right_inv := fun _ ↦ Subtype.ext (by group) }
    fun h₂ x ↦ by
      show g • ((g⁻¹ * (h₂ : G_outer) * g) • x) = (h₂ : G_outer) • (g • x)
      simp only [smul_smul, mul_inv_cancel_left, mul_assoc]

/-- **AE-disjointness of arbitrary `G_outer`-translates related by an `H`-element.**
Let `D` be a fundamental domain for a subgroup `H ≤ G_outer` acting on `α` with a
`G_outer`-invariant measure `μ`. For any pair `g₁, g₂ ∈ G_outer` whose relative
position `g₁⁻¹ * g₂` lies in `H` and is non-trivial, the translates `g₁ • D` and
`g₂ • D` are `AE`-disjoint with respect to `μ`. -/
theorem IsFundamentalDomain.aedisjoint_smul_of_mul_inv_mem
    {G_outer α : Type*} [Group G_outer] [MeasurableSpace α] [MulAction G_outer α]
    {μ : Measure α} [SMulInvariantMeasure G_outer α μ]
    {H : Subgroup G_outer} {D : Set α} (hD : IsFundamentalDomain H D μ)
    {g₁ g₂ : G_outer} (h_mem : g₁⁻¹ * g₂ ∈ H) (h_ne : g₁⁻¹ * g₂ ≠ 1) :
    AEDisjoint μ (g₁ • D) (g₂ • D) := by
  have h_core : AEDisjoint μ ((1 : H) • D) ((⟨g₁⁻¹ * g₂, h_mem⟩ : H) • D) := by
    refine hD.aedisjoint ?_
    intro heq
    apply h_ne
    simpa [Subgroup.coe_one, eq_comm] using congr_arg (Subtype.val : H → G_outer) heq
  rw [show ((1 : H) • D : Set α) = D from one_smul H D,
    show ((⟨g₁⁻¹ * g₂, h_mem⟩ : H) • D : Set α) = (g₁⁻¹ * g₂) • D from rfl] at h_core
  have h_inter : (g₁ • D) ∩ (g₂ • D) = g₁ • (D ∩ ((g₁⁻¹ * g₂) • D)) := by
    rw [Set.smul_set_inter, ← mul_smul, mul_inv_cancel_left]
  show μ ((g₁ • D) ∩ (g₂ • D)) = 0
  rw [h_inter, measure_smul]
  exact h_core

end MeasureTheory

/-! ### PSL-coset fundamental domain for `imageGamma1_PSL N`

Since `Γ₁(N) ⊆ SL(2,ℤ)` does not act faithfully on `ℍ` (the `±I` subgroup acts
trivially), the genuine `IsFundamentalDomain` statement is phrased via the image
of `Γ₁(N)` in `PSL(2,ℤ)`. -/

/-- The image of `Γ₁(N) ⊆ SL(2,ℤ)` in `PSL(2,ℤ) = SL(2,ℤ) / {±I}`. -/
noncomputable def imageGamma1_PSL (N : ℕ) [NeZero N] : Subgroup PSL(2, ℤ) :=
  (Gamma1 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- Image of a finite-index subgroup under a surjection has finite index. -/
instance imageGamma1_PSL_finiteIndex : (imageGamma1_PSL N).FiniteIndex := by
  refine ⟨fun h ↦ ?_⟩
  have h_dvd : (imageGamma1_PSL N).index ∣ (Gamma1 N).index := by
    apply Subgroup.index_map_dvd
    exact QuotientGroup.mk_surjective
  rw [h] at h_dvd
  exact Subgroup.FiniteIndex.index_ne_zero (Nat.eq_zero_of_zero_dvd h_dvd)

instance instCountable_PSL_quotient_imageGamma1 :
    Countable (PSL(2, ℤ) ⧸ imageGamma1_PSL N) :=
  Quotient.countable

noncomputable instance instFintype_PSL_quotient_imageGamma1 :
    Fintype (PSL(2, ℤ) ⧸ imageGamma1_PSL N) :=
  Subgroup.fintypeQuotientOfFiniteIndex

/-- The PSL-coset tiling: union of `(q.out)⁻¹ • fdo` over `q ∈ PSL(2,ℤ) ⧸ imageGamma1_PSL N`. -/
noncomputable def Gamma1_fundDomain_PSL (N : ℕ) [NeZero N] : Set UpperHalfPlane :=
  ⋃ q : PSL(2, ℤ) ⧸ imageGamma1_PSL N, ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set UpperHalfPlane)

/-- **The Γ₁(N)-fundamental domain.** The PSL-coset tiling
`Gamma1_fundDomain_PSL N` is a fundamental domain for the image of `Γ₁(N)` in
`PSL(2,ℤ)` acting on `ℍ` with the hyperbolic measure. -/
theorem isFundamentalDomain_Gamma1_PSL :
    IsFundamentalDomain (imageGamma1_PSL N) (Gamma1_fundDomain_PSL N) μ_hyp :=
  isFundamentalDomain_fdo_PSL.subgroup_iUnion_out_smul (imageGamma1_PSL N)

/-- Distinct PSL-coset tiles `(q.out)⁻¹ • fdo` are pairwise a.e.-disjoint. -/
theorem aedisjoint_PSL_coset_tiles :
    Pairwise (fun q₁ q₂ : PSL(2, ℤ) ⧸ imageGamma1_PSL N ↦
      AEDisjoint μ_hyp ((q₁.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))
        ((q₂.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))) := by
  intro q₁ q₂ hne
  have h_inv_ne : (q₁.out : PSL(2, ℤ))⁻¹ ≠ (q₂.out : PSL(2, ℤ))⁻¹ := by
    intro hg
    apply hne
    rw [← q₁.out_eq, ← q₂.out_eq, inv_injective hg]
  exact isFundamentalDomain_fdo_PSL.aedisjoint h_inv_ne

/-- Each PSL-coset tile is null-measurable. -/
theorem nullMeasurableSet_PSL_coset_tile (q : PSL(2, ℤ) ⧸ imageGamma1_PSL N) :
    NullMeasurableSet ((q.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ)) μ_hyp :=
  isFundamentalDomain_fdo_PSL.nullMeasurableSet_smul _

/-- **Integral over the Γ₁(N)-fundamental domain decomposes as a tile sum.** For
an integrable function `h`, the integral over `Gamma1_fundDomain_PSL N` equals
the finite sum of integrals over each PSL-coset tile. -/
theorem setIntegral_Gamma1_fundDomain_PSL_eq_sum
    (h : ℍ → ℂ)
    (h_int : IntegrableOn h (Gamma1_fundDomain_PSL N) μ_hyp) :
    ∫ τ in Gamma1_fundDomain_PSL N, h τ ∂μ_hyp =
      ∑ q : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
        ∫ τ in ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  rw [Gamma1_fundDomain_PSL,
    integral_iUnion_ae nullMeasurableSet_PSL_coset_tile aedisjoint_PSL_coset_tiles h_int,
    tsum_fintype]

/-- The Γ₁(N)-fundamental domain `Gamma1_fundDomain_PSL N` has finite hyperbolic
measure. -/
theorem hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top :
    μ_hyp (Gamma1_fundDomain_PSL N) < ⊤ := by
  rw [Gamma1_fundDomain_PSL]
  refine lt_of_le_of_lt (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun q' _ ↦ ?_
  rw [(isFundamentalDomain_fdo_PSL.smul _).measure_eq isFundamentalDomain_fdo_PSL]
  exact lt_of_le_of_lt (measure_mono fdo_subset_fd) hyperbolicMeasure_fd_lt_top

/-- The Petersson integrand `petersson k f g` is integrable on the Γ₁(N)-
fundamental domain `Gamma1_fundDomain_PSL N` for two `Γ₁(N)`-cusp forms. -/
theorem integrableOn_petersson_Gamma1_fundDomain_PSL
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IntegrableOn (fun τ ↦ petersson k ⇑f ⇑g τ)
      (Gamma1_fundDomain_PSL N) μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f g
  exact IntegrableOn.of_bound hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous g)).aestronglyMeasurable.restrict)
    C (ae_of_all _ fun τ ↦ hC τ)

/-! ### Γ₁(N) coset-tiling fundamental-domain API -/

/-- Synonym: image of `Γ₁(N)` in the faithful `PSL(2,ℤ)`-action group on `ℍ`. -/
noncomputable abbrev imageGamma1 (N : ℕ) [NeZero N] : Subgroup PSL(2, ℤ) :=
  imageGamma1_PSL N

/-- Synonym: the Γ₁(N) coset-tiling fundamental domain in `ℍ`, indexed by the
PSL-coset space `PSL(2,ℤ) ⧸ imageGamma1 N`. -/
noncomputable abbrev Gamma1_fundDomain (N : ℕ) [NeZero N] : Set UpperHalfPlane :=
  Gamma1_fundDomain_PSL N

/-- The Γ₁(N) coset tiling `Gamma1_fundDomain N` is a fundamental domain for the
image of `Γ₁(N)` in `PSL(2,ℤ)` acting on `ℍ` with the hyperbolic measure. -/
theorem isFundamentalDomain_Gamma1_coset_tiling :
    IsFundamentalDomain (imageGamma1 N) (Gamma1_fundDomain N) μ_hyp :=
  isFundamentalDomain_Gamma1_PSL

/-- Shifting `Gamma1_fundDomain N` by any element `g` of the subgroup
`imageGamma1 N` again yields a fundamental domain for that same subgroup. -/
theorem isFundamentalDomain_Gamma1_smul (g : imageGamma1 N) :
    IsFundamentalDomain (imageGamma1 N) (g • Gamma1_fundDomain N) μ_hyp :=
  isFundamentalDomain_Gamma1_coset_tiling.smul g

/-- Integrals of any function over two `imageGamma1 N`-fundamental domains agree,
provided the integrand is invariant under the `imageGamma1 N`-action. -/
theorem setIntegral_Gamma1_fundDomain_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D D' : Set UpperHalfPlane}
    (hD : IsFundamentalDomain (imageGamma1 N) D μ_hyp)
    (hD' : IsFundamentalDomain (imageGamma1 N) D' μ_hyp)
    {h : UpperHalfPlane → E}
    (h_inv : ∀ (γ : imageGamma1 N) (τ : UpperHalfPlane), h (γ • τ) = h τ) :
    ∫ τ in D, h τ ∂μ_hyp = ∫ τ in D', h τ ∂μ_hyp :=
  hD.setIntegral_eq hD' h_inv

/-- For `α : PSL(2, ℤ)` in the normalizer of `imageGamma1 N`, the shifted tiling
`α • Gamma1_fundDomain N` is again a fundamental domain for `imageGamma1 N`
acting on `ℍ`. -/
theorem isFundamentalDomain_Gamma1_shift
    {α : PSL(2, ℤ)} (hα : α ∈ (imageGamma1 N).normalizer) :
    IsFundamentalDomain (imageGamma1 N) (α • Gamma1_fundDomain N) μ_hyp :=
  isFundamentalDomain_Gamma1_coset_tiling.smul_of_mem_normalizer hα

/-! ### Γ₁(N) projective fundamental domain at the `PSL(2, ℝ)` ambient -/

open scoped MatrixGroups

/-- The projective image of `Γ₁(N)` inside `PSL(2, ℝ)`, obtained by composing the
integer projection `Γ₁(N) → PSL(2, ℤ) = imageGamma1_PSL N` with the descended
real cast `PSL2Z_to_PSL2R : PSL(2, ℤ) →* PSL(2, ℝ)`. -/
noncomputable def imageGamma1_PSL_R (N : ℕ) [NeZero N] : Subgroup PSL(2, ℝ) :=
  (imageGamma1_PSL N).map PSL2Z_to_PSL2R

/-- The same set `Gamma1_fundDomain_PSL N : Set ℍ` that serves as the
`imageGamma1_PSL N`-fundamental domain at the `PSL(2, ℤ)` ambient is also an
`imageGamma1_PSL_R N`-fundamental domain at the `PSL(2, ℝ)` ambient. -/
theorem isFundamentalDomain_Gamma1_PSL_R :
    IsFundamentalDomain (imageGamma1_PSL_R N) (Gamma1_fundDomain_PSL N) μ_hyp := by
  have h_image_eq : (Equiv.refl ℍ) '' (Gamma1_fundDomain_PSL N) = Gamma1_fundDomain_PSL N := by
    simp
  rw [← h_image_eq]
  refine isFundamentalDomain_Gamma1_PSL.image_of_equiv (Equiv.refl ℍ)
    (MeasureTheory.Measure.QuasiMeasurePreserving.id μ_hyp)
    ((Subgroup.equivMapOfInjective (imageGamma1_PSL N) PSL2Z_to_PSL2R
      PSL2Z_to_PSL2R_injective).toEquiv.symm) ?_
  intro g τ
  show (Equiv.refl ℍ) (((Subgroup.equivMapOfInjective (imageGamma1_PSL N)
        PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.symm g : imageGamma1_PSL N) • τ) =
      ((g : imageGamma1_PSL_R N) : PSL(2, ℝ)) • (Equiv.refl ℍ) τ
  simp only [Equiv.refl_apply]
  set g' : imageGamma1_PSL N := (Subgroup.equivMapOfInjective (imageGamma1_PSL N)
    PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.symm g
  have h_g_coe :
      ((g : imageGamma1_PSL_R N) : PSL(2, ℝ)) = PSL2Z_to_PSL2R (g' : PSL(2, ℤ)) := by
    rw [← Subgroup.coe_equivMapOfInjective_apply (imageGamma1_PSL N) PSL2Z_to_PSL2R
      PSL2Z_to_PSL2R_injective g']
    congr 1
    exact ((Subgroup.equivMapOfInjective (imageGamma1_PSL N) PSL2Z_to_PSL2R
      PSL2Z_to_PSL2R_injective).toEquiv.apply_symm_apply g).symm
  rw [h_g_coe, PSL2Z_to_PSL2R_smul_eq]
  rfl

/-- Transfer of an `IsFundamentalDomain` claim from the projective-real subgroup
`imageGamma1_PSL_R N : Subgroup PSL(2, ℝ)` to the projective-integer subgroup
`imageGamma1_PSL N : Subgroup PSL(2, ℤ)`; the reverse of
`isFundamentalDomain_Gamma1_PSL_R`. -/
theorem isFundamentalDomain_imageGamma1_PSL_of_PSL_R
    {S : Set UpperHalfPlane}
    (hS : IsFundamentalDomain (imageGamma1_PSL_R N) S μ_hyp) :
    IsFundamentalDomain (imageGamma1_PSL N) S μ_hyp := by
  have h_image_eq : (Equiv.refl ℍ) '' S = S := by simp
  rw [← h_image_eq]
  refine hS.image_of_equiv (Equiv.refl ℍ)
    (MeasureTheory.Measure.QuasiMeasurePreserving.id μ_hyp)
    ((Subgroup.equivMapOfInjective (imageGamma1_PSL N) PSL2Z_to_PSL2R
      PSL2Z_to_PSL2R_injective).toEquiv) ?_
  intro g τ
  show (Equiv.refl ℍ) (((Subgroup.equivMapOfInjective (imageGamma1_PSL N)
        PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv g : imageGamma1_PSL_R N) • τ) =
      ((g : imageGamma1_PSL N) : PSL(2, ℤ)) • (Equiv.refl ℍ) τ
  simp only [Equiv.refl_apply]
  show (((Subgroup.equivMapOfInjective (imageGamma1_PSL N) PSL2Z_to_PSL2R
        PSL2Z_to_PSL2R_injective).toEquiv g : imageGamma1_PSL_R N) :
        PSL(2, ℝ)) • τ =
      ((g : imageGamma1_PSL N) : PSL(2, ℤ)) • τ
  have h_g_coe :
      ((((Subgroup.equivMapOfInjective (imageGamma1_PSL N) PSL2Z_to_PSL2R
        PSL2Z_to_PSL2R_injective).toEquiv g) : imageGamma1_PSL_R N) : PSL(2, ℝ)) =
      PSL2Z_to_PSL2R ((g : imageGamma1_PSL N) : PSL(2, ℤ)) :=
    Subgroup.coe_equivMapOfInjective_apply _ _ _ _
  rw [h_g_coe, PSL2Z_to_PSL2R_smul_eq]

/-- The direct integer-to-projective-real map `SL2Z_to_PSL2R` produces the same
`Γ₁(N)`-image as the two-step composition through `imageGamma1_PSL N`:
`(Γ₁(N)).map SL2Z_to_PSL2R = imageGamma1_PSL_R N`. -/
theorem map_SL2Z_to_PSL2R_eq_imageGamma1_PSL_R :
    (Gamma1 N).map SL2Z_to_PSL2R = imageGamma1_PSL_R N := by
  unfold imageGamma1_PSL_R imageGamma1_PSL
  rw [Subgroup.map_map]
  rfl

/-! ### SL/Γ₁(N) → PSL/imageGamma1_PSL(N) quotient bridge -/

/-- Natural quotient map `SL(2,ℤ) ⧸ Gamma1 N → PSL(2,ℤ) ⧸ imageGamma1_PSL N`,
sending each `Γ₁(N)`-coset `[g]` to its `imageGamma1_PSL N`-coset `[PSL.mk g]`. -/
noncomputable def slToPslQuot :
    SL(2, ℤ) ⧸ Gamma1 N → PSL(2, ℤ) ⧸ imageGamma1_PSL N :=
  Quotient.lift
    (fun g : SL(2, ℤ) ↦
      (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ imageGamma1_PSL N))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply (QuotientGroup.eq).mpr
      have h_psl : (QuotientGroup.mk a : PSL(2, ℤ))⁻¹ * QuotientGroup.mk b =
          QuotientGroup.mk (a⁻¹ * b) := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rw [h_psl]
      exact ⟨a⁻¹ * b, hab, rfl⟩)

@[simp]
theorem slToPslQuot_mk (g : SL(2, ℤ)) :
    slToPslQuot (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :=
  rfl

/-- The natural map `SL(2,ℤ) ⧸ Gamma1 N → PSL(2,ℤ) ⧸ imageGamma1_PSL N` is surjective. -/
theorem slToPslQuot_surjective : Function.Surjective (slToPslQuot (N := N)) := by
  intro q'
  obtain ⟨g_psl, hg_psl⟩ := QuotientGroup.mk_surjective q'
  obtain ⟨g_sl, hg_sl⟩ := QuotientGroup.mk_surjective g_psl
  refine ⟨QuotientGroup.mk g_sl, ?_⟩
  rw [slToPslQuot_mk, hg_sl, hg_psl]

/-! #### Left-multiplication action of `SL(2, ℤ)` on the coset space `SL(2, ℤ) ⧸ Gamma1 N` -/

/-- Left multiplication by `h : SL(2, ℤ)` is a well-defined map on `SL(2, ℤ) ⧸ Gamma1 N`. -/
noncomputable def slLeftMul (h : SL(2, ℤ)) :
    SL(2, ℤ) ⧸ Gamma1 N → SL(2, ℤ) ⧸ Gamma1 N :=
  Quotient.lift (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk (h * g) : SL(2, ℤ) ⧸ Gamma1 N))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply QuotientGroup.eq.mpr
      have : (h * a)⁻¹ * (h * b) = a⁻¹ * b := by group
      rw [this]; exact hab)

@[simp]
theorem slLeftMul_mk (h g : SL(2, ℤ)) :
    slLeftMul h (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk (h * g) :=
  rfl

theorem slLeftMul_one (q : SL(2, ℤ) ⧸ Gamma1 N) : slLeftMul 1 q = q := by
  induction q using QuotientGroup.induction_on with
  | _ g => simp

theorem slLeftMul_comp (h₁ h₂ : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    slLeftMul h₁ (slLeftMul h₂ q) = slLeftMul (h₁ * h₂) q := by
  induction q using QuotientGroup.induction_on with
  | _ g => simp [mul_assoc]

/-- `slLeftMul h` is a bijection, with inverse `slLeftMul h⁻¹`. -/
noncomputable def slLeftMulEquiv (h : SL(2, ℤ)) :
    SL(2, ℤ) ⧸ Gamma1 N ≃ SL(2, ℤ) ⧸ Gamma1 N where
  toFun := slLeftMul h
  invFun := slLeftMul h⁻¹
  left_inv q := by rw [slLeftMul_comp, inv_mul_cancel, slLeftMul_one]
  right_inv q := by rw [slLeftMul_comp, mul_inv_cancel, slLeftMul_one]

/-- **SL-equivariance of `slToPslQuot`.** For `h : SL(2,ℤ)` and `q : SL/Γ₁`:
`slToPslQuot (h · q) = (PSL.mk h) · slToPslQuot q` where `·` on the RHS is the
PSL-action on `PSL(2,ℤ) ⧸ imageGamma1_PSL N`. -/
theorem slToPslQuot_slLeftMul (h : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    slToPslQuot (slLeftMul h q) =
      Quotient.map' (fun x : PSL(2, ℤ) ↦ (QuotientGroup.mk h : PSL(2, ℤ)) * x)
        (by
          intro a b hab
          change (QuotientGroup.leftRel _).r _ _ at hab
          change (QuotientGroup.leftRel _).r _ _
          rw [QuotientGroup.leftRel_apply] at hab
          rw [QuotientGroup.leftRel_apply]
          have : ((QuotientGroup.mk h : PSL(2, ℤ)) * a)⁻¹ *
              ((QuotientGroup.mk h : PSL(2, ℤ)) * b) = a⁻¹ * b := by group
          rw [this]; exact hab)
        (slToPslQuot q) := by
  induction q using QuotientGroup.induction_on with
  | _ g =>
    show slToPslQuot (QuotientGroup.mk (h * g)) = _
    simp only [slToPslQuot_mk]
    show (QuotientGroup.mk (QuotientGroup.mk (h * g) : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ imageGamma1_PSL N) = _
    rw [show (QuotientGroup.mk (h * g) : PSL(2, ℤ)) =
        (QuotientGroup.mk h : PSL(2, ℤ)) * (QuotientGroup.mk g : PSL(2, ℤ)) from
      (QuotientGroup.mk_mul _ _ _).symm]
    rfl

private theorem slToPslQuot_slLeftMul_eq_of_eq (h : SL(2, ℤ)) (q : SL(2, ℤ) ⧸ Gamma1 N)
    (gs gt : SL(2, ℤ))
    (hq : slToPslQuot q = QuotientGroup.mk (QuotientGroup.mk gs : PSL(2, ℤ)))
    (hh : (QuotientGroup.mk h : PSL(2, ℤ)) =
      QuotientGroup.mk gt * (QuotientGroup.mk gs)⁻¹) :
    slToPslQuot (slLeftMul h q) = QuotientGroup.mk (QuotientGroup.mk gt : PSL(2, ℤ)) := by
  rw [slToPslQuot_slLeftMul h q, hq]
  show (QuotientGroup.mk ((QuotientGroup.mk h : PSL(2, ℤ)) *
    (QuotientGroup.mk gs : PSL(2, ℤ))) : PSL(2, ℤ) ⧸ imageGamma1_PSL N) = _
  rw [hh]; congr 1; group

/-- **Uniform fiber size**: any two fibers of `slToPslQuot` have equal
cardinality. -/
theorem slToPslQuot_fiber_card_uniform
    (q₁' q₂' : PSL(2, ℤ) ⧸ imageGamma1_PSL N) :
    haveI : DecidableEq (PSL(2, ℤ) ⧸ imageGamma1_PSL N) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
        slToPslQuot q = q₁')).card =
      (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
        slToPslQuot q = q₂')).card := by
  haveI : DecidableEq (PSL(2, ℤ) ⧸ imageGamma1_PSL N) := Classical.decEq _
  obtain ⟨q₁, hq₁⟩ := slToPslQuot_surjective q₁'
  obtain ⟨q₂, hq₂⟩ := slToPslQuot_surjective q₂'
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  set h := g₂ * g₁⁻¹ with hh_def
  refine Finset.card_bij'
    (fun q _ ↦ slLeftMul h q)
    (fun q _ ↦ slLeftMul h⁻¹ q)
    (fun q hq ↦ ?_)
    (fun q hq ↦ ?_)
    (fun q _ ↦ by
      show slLeftMul h⁻¹ (slLeftMul h q) = q
      rw [slLeftMul_comp, inv_mul_cancel, slLeftMul_one])
    (fun q _ ↦ by
      show slLeftMul h (slLeftMul h⁻¹ q) = q
      rw [slLeftMul_comp, mul_inv_cancel, slLeftMul_one])
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [show q₂' = QuotientGroup.mk (QuotientGroup.mk g₂ : PSL(2, ℤ)) from by
      rw [← slToPslQuot_mk]; exact hq₂.symm]
    refine slToPslQuot_slLeftMul_eq_of_eq h q g₁ g₂ ?_ ?_
    · rw [hq, ← slToPslQuot_mk]; exact hq₁.symm
    · rw [hh_def, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [show q₁' = QuotientGroup.mk (QuotientGroup.mk g₁ : PSL(2, ℤ)) from by
      rw [← slToPslQuot_mk]; exact hq₁.symm]
    refine slToPslQuot_slLeftMul_eq_of_eq h⁻¹ q g₂ g₁ ?_ ?_
    · rw [hq, ← slToPslQuot_mk]; exact hq₂.symm
    · rw [hh_def, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]; group

private lemma PSL_smul_set_eq_SL (g : SL(2, ℤ)) (S : Set ℍ) :
    ((QuotientGroup.mk g : PSL(2, ℤ))) • S = (g : SL(2, ℤ)) • S := rfl

private lemma PSL_inv_smul_set_eq_SL (g : SL(2, ℤ)) (S : Set ℍ) :
    ((QuotientGroup.mk g : PSL(2, ℤ)))⁻¹ • S = (g : SL(2, ℤ))⁻¹ • S := by
  rw [show ((QuotientGroup.mk g : PSL(2, ℤ)))⁻¹ =
        (QuotientGroup.mk g⁻¹ : PSL(2, ℤ)) from
      (QuotientGroup.mk_inv _ g).symm,
    PSL_smul_set_eq_SL g⁻¹ S]

/-- **Fiber-invariance of the SL-tile integral.** For a `Γ₁(N)`-invariant function
`h`, the integral over the SL-tile `q.out⁻¹ • fdo` equals the integral over the
corresponding PSL-tile `(slToPslQuot q).out⁻¹ • fdo`. -/
theorem setIntegral_SL_tile_eq_PSL_tile (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp =
      ∫ τ in ((slToPslQuot q).out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  have h_quot_eq :
      (QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ imageGamma1_PSL N) =
      QuotientGroup.mk ((slToPslQuot q).out : PSL(2, ℤ)) := by
    have h1 : slToPslQuot q =
        QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) := by
      conv_lhs => rw [← q.out_eq]
      rfl
    exact h1.symm.trans (slToPslQuot q).out_eq.symm
  rw [QuotientGroup.eq] at h_quot_eq
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := h_quot_eq
  have h_eq_PSL : ((slToPslQuot q).out : PSL(2, ℤ)) =
      QuotientGroup.mk q.out * QuotientGroup.mk γ := by
    have h_mul : (QuotientGroup.mk q.out : PSL(2, ℤ)) *
        ((QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ * (slToPslQuot q).out) =
        (slToPslQuot q).out := by group
    rw [← h_mul, ← hγ_eq]
    rfl
  rw [show ((slToPslQuot q).out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ) =
      ((QuotientGroup.mk γ : PSL(2, ℤ))⁻¹ •
        ((QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))) from by
      rw [h_eq_PSL, mul_inv_rev, mul_smul]]
  rw [PSL_inv_smul_set_eq_SL q.out fdo, PSL_inv_smul_set_eq_SL γ _]
  symm
  rw [show ((γ⁻¹ : SL(2, ℤ)) • ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) : Set ℍ) =
      (fun τ ↦ (γ⁻¹ : SL(2, ℤ)) • τ) '' ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) from rfl,
    (measurePreserving_smul (γ⁻¹ : SL(2, ℤ)) μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]
  congr 1; ext τ
  exact h_inv γ⁻¹ ((Gamma1 N).inv_mem hγ_mem) τ

open Classical in
/-- **SL→PSL fiber sum reindexing** for `Γ₁(N)`-invariant integrands. The
SL-coset sum of integrals `∑_{q : SL/Γ₁(N)} ∫_{q.out⁻¹•fdo} h dμ` reindexes along
the natural map `slToPslQuot : SL/Γ₁(N) → PSL/imageGamma1_PSL(N)` as a weighted
PSL-coset sum, with each PSL-coset weighted by its fiber cardinality. -/
theorem sum_SL_tile_eq_fiberwise_PSL_tile (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp =
      ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
        (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
          slToPslQuot q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  calc ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in ((slToPslQuot q).out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_eq_PSL_tile h h_inv q
    _ = ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
          ∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
            slToPslQuot q = q'),
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        (Finset.sum_fiberwise' Finset.univ (slToPslQuot (N := N))
          (fun q' ↦ ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp)).symm
    _ = ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
            slToPslQuot q = q')).card •
              ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        exact Finset.sum_const _

/-! ### Right-translate reindexing of `SL(2, ℤ) ⧸ Γ₁(N)` by `Γ₀(N)` elements -/

/-- Reindexing equivalence on `SL(2, ℤ) ⧸ Γ₁(N)` by right-multiplication by `γ⁻¹`
for `γ ∈ Γ₀(N)` (well-defined since `γ` normalizes `Γ₁(N)`). The forward
direction sends `[δ] ↦ [δ * γ⁻¹]`. -/
noncomputable def Gamma1QuotEquivOfGamma0
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    SL(2, ℤ) ⧸ Gamma1 N ≃ SL(2, ℤ) ⧸ Gamma1 N where
  toFun := Quotient.map (· * γ⁻¹) (by
    intro a b hab; change (QuotientGroup.leftRel _).r _ _
    change (QuotientGroup.leftRel _).r _ _ at hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [show (a * γ⁻¹)⁻¹ * (b * γ⁻¹) = γ * (a⁻¹ * b) * γ⁻¹ from by group]
    exact HeckeRing.GL2.Gamma0_normalizes_Gamma1 ⟨γ, hγ⟩ _ hab)
  invFun := Quotient.map (· * γ) (by
    intro a b hab; change (QuotientGroup.leftRel _).r _ _
    change (QuotientGroup.leftRel _).r _ _ at hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [show (a * γ)⁻¹ * (b * γ) = γ⁻¹ * (a⁻¹ * b) * γ from by group]
    convert HeckeRing.GL2.Gamma0_normalizes_Gamma1
      ⟨γ⁻¹, (Gamma0 N).inv_mem hγ⟩ _ hab using 1
    simp [mul_assoc])
  left_inv := fun q ↦ by induction q using Quotient.inductionOn with
    | h δ => simp [Quotient.map_mk, mul_assoc]
  right_inv := fun q ↦ by induction q using Quotient.inductionOn with
    | h δ => simp [Quotient.map_mk, mul_assoc]

@[simp]
theorem Gamma1QuotEquivOfGamma0_mk (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N)
    (δ : SL(2, ℤ)) :
    Gamma1QuotEquivOfGamma0 γ hγ ⟦δ⟧ = ⟦δ * γ⁻¹⟧ := rfl

/-- The Petersson integrand `petersson k f g` is `Γ₁(N)`-invariant: for `γ ∈ Γ₁(N)`,
`petersson k f g (γ • τ) = petersson k f g τ`. -/
theorem petersson_Gamma1_invariant (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) (τ : UpperHalfPlane) :
    petersson k ⇑f ⇑g (γ • τ) = petersson k ⇑f ⇑g τ := by
  rw [← petersson_slash_SL, slash_Gamma1_eq f γ hγ, slash_Gamma1_eq g γ hγ]

/-- The Petersson integrand is invariant under the `imageGamma1 N`-action on `ℍ`:
for `γ : imageGamma1 N` and `τ : ℍ`, `petersson k f g (γ • τ) = petersson k f g τ`. -/
theorem petersson_imageGamma1_invariant (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : imageGamma1 N) (τ : UpperHalfPlane) :
    petersson k ⇑f ⇑g (γ • τ) = petersson k ⇑f ⇑g τ := by
  obtain ⟨δ, hδ_mem, hδ_eq⟩ := γ.2
  show petersson k ⇑f ⇑g ((γ : PSL(2, ℤ)) • τ) = _
  rw [← hδ_eq]
  exact petersson_Gamma1_invariant f g δ hδ_mem τ

/-- Each `petN` summand equals an integral over a translate of `fd`:
`peterssonInner k fd (f∣q⁻¹) (g∣q⁻¹) = ∫_{q⁻¹ • fd} petersson k f g dμ`. -/
theorem petN_summand_eq_setIntegral
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    peterssonInner k fd (⇑f ∣[k] q.out⁻¹) (⇑g ∣[k] q.out⁻¹) =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
        petersson k ⇑f ⇑g τ ∂μ_hyp := by
  simp only [peterssonInner]; simp_rw [petersson_slash_SL]
  rw [← Set.image_smul,
    ← (measurePreserving_smul q.out⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]

/-- Integral over a `Γ₁(N)`-translate of any `SL₂(ℤ)`-coset tile equals the
integral over the original tile, for `Γ₁(N)`-invariant integrands ([DS] Lemma
5.5.1): for `η ∈ Γ₁(N)` and any set `S`, `∫_{η • S} h dμ = ∫_S h dμ` when
`h(η • τ) = h(τ)`. -/
theorem setIntegral_Gamma1_smul_eq
    (h : UpperHalfPlane → ℂ) (η : SL(2, ℤ)) (_hη : η ∈ Gamma1 N)
    (h_inv : ∀ τ, h (η • τ) = h τ) (S : Set UpperHalfPlane) :
    ∫ τ in η • S, h τ ∂μ_hyp = ∫ τ in S, h τ ∂μ_hyp := by
  rw [show (η • S : Set ℍ) = (fun τ ↦ η • τ) '' S from rfl,
    (measurePreserving_smul η μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul η)]
  congr 1; ext τ; exact h_inv τ

/-- Specialization of `setIntegral_Gamma1_smul_eq` to the Petersson integrand of
two `Γ₁(N)`-cusp forms: for `η ∈ Γ₁(N)` and any set `S ⊆ ℍ`,
`∫_{η • S} petersson k f g dμ = ∫_S petersson k f g dμ`. -/
theorem setIntegral_Gamma1_smul_petersson
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (η : SL(2, ℤ)) (hη : η ∈ Gamma1 N) (S : Set UpperHalfPlane) :
    ∫ τ in η • S, petersson k ⇑f ⇑g τ ∂μ_hyp =
      ∫ τ in S, petersson k ⇑f ⇑g τ ∂μ_hyp :=
  setIntegral_Gamma1_smul_eq _ η hη
    (fun τ ↦ petersson_Gamma1_invariant f g η hη τ) S

/-- The integral over the SL₂(ℤ)-translate `δ • S` of a `Γ₁(N)`-invariant function
can be reduced to an integral over `S`: `∫_{δ • S} h dμ = ∫_S h(δ • ·) dμ`. -/
theorem setIntegral_smul_eq
    (h : UpperHalfPlane → ℂ) (δ : SL(2, ℤ)) (S : Set UpperHalfPlane) :
    ∫ τ in δ • S, h τ ∂μ_hyp = ∫ τ in S, h (δ • τ) ∂μ_hyp := by
  rw [show (δ • S : Set ℍ) = (fun τ ↦ δ • τ) '' S from rfl,
    (measurePreserving_smul δ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul δ)]

/-! ### Diamond unitarity

Diamond unitarity `petN (⟨d⟩f) (⟨d⟩g) = petN f g` ([DS] Theorem 5.5.3,
[Miy] Thm 4.5.4) says the level-N inner product is preserved by diamond
operators. -/

/-- Diamond unitarity for the level-N Petersson inner product:
the inner product of slashed cusp forms equals the original inner product.

For `γ ∈ Γ₀(N)` (representing diamond operator `⟨d⟩`), `f∣γ` and `g∣γ` are
cusp forms for `Γ₁(N)`, and `petN (f∣γ) (g∣γ) = petN f g`. -/
theorem petN_slash_invariant
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (_hf : ∀ η ∈ Gamma1 N, ⇑f ∣[k] η = ⇑f)
    (_hg : ∀ η ∈ Gamma1 N, ⇑g ∣[k] η = ⇑g)
    (f' g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf' : ⇑f' = ⇑f ∣[k] γ) (hg' : ⇑g' = ⇑g ∣[k] γ) :
    petN f' g' = petN f g := by
  simp only [petN]
  set σ : SL(2, ℤ) ⧸ Gamma1 N ≃ SL(2, ℤ) ⧸ Gamma1 N :=
    Gamma1QuotEquivOfGamma0 γ hγ
  have out_mem : ∀ δ : SL(2, ℤ), (⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹ * δ ∈ Gamma1 N :=
    fun δ ↦ by
      have h := Quotient.exact ((⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out_eq)
      change (QuotientGroup.leftRel _).r _ _ at h
      rwa [QuotientGroup.leftRel_apply] at h
  have G1_tile : ∀ (η : SL(2, ℤ)), η ∈ Gamma1 N → ∀ S : Set ℍ,
      ∫ τ in η • S, petersson k (⇑f) (⇑g) τ ∂μ_hyp =
      ∫ τ in S, petersson k (⇑f) (⇑g) τ ∂μ_hyp := fun η hη S ↦ by
    rw [show (η • S : Set ℍ) = (fun τ ↦ η • τ) '' S from rfl,
      (measurePreserving_smul η μ_hyp).setIntegral_image_emb (measurableEmbedding_const_smul η)]
    congr 1; ext τ; rw [← petersson_slash_SL, slash_Gamma1_eq f η hη, slash_Gamma1_eq g η hη]
  suffices key : ∀ q, peterssonInner k fd (⇑f' ∣[k] q.out⁻¹) (⇑g' ∣[k] q.out⁻¹) =
      peterssonInner k fd (⇑f ∣[k] (σ q).out⁻¹) (⇑g ∣[k] (σ q).out⁻¹) by
    simp_rw [key]
    exact σ.sum_comp (fun q ↦ peterssonInner k fd (⇑f ∣[k] q.out⁻¹) (⇑g ∣[k] q.out⁻¹))
  intro q; induction q using Quotient.inductionOn with | h δ => ?_
  rw [show peterssonInner k fd (⇑f' ∣[k] (⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹)
      (⇑g' ∣[k] (⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹) =
    peterssonInner k fd (⇑f ∣[k] (γ * (⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹))
      (⇑g ∣[k] (γ * (⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹)) from by
    congr 1 <;> [rw [hf']; rw [hg']] <;> rw [← SlashAction.slash_mul]]
  simp only [peterssonInner]; simp_rw [petersson_slash_SL]
  rw [← MeasurePreserving.setIntegral_image_emb (measurePreserving_smul
        (γ * (⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹) μ_hyp)
        (measurableEmbedding_const_smul _) _ fd, Set.image_smul,
    ← MeasurePreserving.setIntegral_image_emb (measurePreserving_smul
        ((σ ⟦δ⟧).out⁻¹) μ_hyp)
        (measurableEmbedding_const_smul _) _ fd, Set.image_smul,
    show σ ⟦δ⟧ = ⟦δ * γ⁻¹⟧ from by simp [σ],
    show γ * (⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹ =
      (γ * (⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹ *
        (⟦δ * γ⁻¹⟧ : SL(2, ℤ) ⧸ Gamma1 N).out) *
      (⟦δ * γ⁻¹⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹ from by group, mul_smul]
  exact G1_tile _ (by
    rw [show γ * (⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹ *
        (⟦δ * γ⁻¹⟧ : SL(2, ℤ) ⧸ Gamma1 N).out =
      ((⟦δ * γ⁻¹⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹ * (δ * γ⁻¹) *
       (γ * ((⟦δ⟧ : SL(2, ℤ) ⧸ Gamma1 N).out⁻¹ * δ)⁻¹ * γ⁻¹))⁻¹ from by group]
    exact (Gamma1 N).inv_mem ((Gamma1 N).mul_mem (out_mem (δ * γ⁻¹))
      (HeckeRing.GL2.Gamma0_normalizes_Gamma1 ⟨γ, hγ⟩ _ ((Gamma1 N).inv_mem (out_mem δ))))) _

/-! ### `petN` as a fiber-weighted PSL-tile sum -/

/-- `∫_{q.out⁻¹ • fd} h dμ = ∫_{q.out⁻¹ • fdo} h dμ` for any `h`: the SL-tile
integrals over `fd` and `fdo` agree (the boundary `fd \ fdo` has measure zero). -/
theorem setIntegral_SL_tile_fd_eq_fdo
    (h : UpperHalfPlane → ℂ) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  rw [show ((q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ) : Set ℍ) =
        (fun τ ↦ (q.out : SL(2, ℤ))⁻¹ • τ) '' (fd : Set ℍ) from rfl,
    (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _),
    show ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ) : Set ℍ) =
        (fun τ ↦ (q.out : SL(2, ℤ))⁻¹ • τ) '' (fdo : Set ℍ) from rfl,
    (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _),
    setIntegral_fd_eq_fdo]

open Classical in
/-- `petN` written as a sum of set-integrals over PSL-coset tiles, weighted by the
fiber cardinality of the SL→PSL quotient map:
```
  petN f g = ∑_{q' : PSL/imageGamma1_PSL N}
               (|fiber q'|) • ∫_{(q'.out)⁻¹ • fdo} petersson k f g dμ_hyp
```  -/
theorem petN_eq_weighted_sum_setIntegral_PSL_tile
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f g =
      ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
        (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
          slToPslQuot q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ),
              petersson k ⇑f ⇑g τ ∂μ_hyp := by
  calc petN f g
      = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹) := rfl
    _ = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
            petersson k ⇑f ⇑g τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ petN_summand_eq_setIntegral f g q
    _ = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ),
            petersson k ⇑f ⇑g τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦
          setIntegral_SL_tile_fd_eq_fdo (petersson k ⇑f ⇑g) q
    _ = ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
            slToPslQuot q = q')).card •
              ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ),
                petersson k ⇑f ⇑g τ ∂μ_hyp :=
        sum_SL_tile_eq_fiberwise_PSL_tile (petersson k ⇑f ⇑g)
          (fun γ hγ τ ↦ petersson_Gamma1_invariant f g γ hγ τ)

/-! ### Uniform fiber count -/

/-- The uniform cardinality of any fiber of `slToPslQuot`, computed at the identity
coset `⟦1⟧`. Uniform by `slToPslQuot_fiber_card_uniform`. -/
noncomputable def slToPslQuot_fiberCard (N : ℕ) [NeZero N] : ℕ :=
  haveI : DecidableEq (PSL(2, ℤ) ⧸ imageGamma1_PSL N) := Classical.decEq _
  (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
    slToPslQuot q =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ imageGamma1_PSL N))).card

/-- Every fiber of `slToPslQuot` has cardinality equal to `slToPslQuot_fiberCard N`. -/
theorem slToPslQuot_fiberCard_eq (q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N) :
    haveI : DecidableEq (PSL(2, ℤ) ⧸ imageGamma1_PSL N) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
      slToPslQuot q = q')).card = slToPslQuot_fiberCard N := by
  rw [slToPslQuot_fiberCard]
  exact slToPslQuot_fiber_card_uniform q' _

open Classical in
/-- With uniform fiber size:
```
  petN f g = c_N • ∑_{q' : PSL/imageGamma1_PSL N} ∫_{q'.out⁻¹•fdo} petersson k f g dμ
```
where `c_N = slToPslQuot_fiberCard N` is the uniform fiber count. -/
theorem petN_eq_nsmul_sum_PSL_tile
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f g = (slToPslQuot_fiberCard N) •
      ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
        ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ),
          petersson k ⇑f ⇑g τ ∂μ_hyp := by
  rw [petN_eq_weighted_sum_setIntegral_PSL_tile f g, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q' _ ↦ ?_
  congr 1
  convert slToPslQuot_fiberCard_eq q' using 2
  congr

/-- `petN` as a single integral over the Γ₁(N)-fundamental domain:
```
  petN f g = c_N • ∫_{D_N^PSL} petersson k f g dμ_hyp
```
where `c_N = slToPslQuot_fiberCard N`. -/
theorem petN_eq_setIntegral_Gamma1_fundDomain_PSL
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f g = (slToPslQuot_fiberCard N) •
      ∫ τ in Gamma1_fundDomain_PSL N, petersson k ⇑f ⇑g τ ∂μ_hyp := by
  rw [petN_eq_nsmul_sum_PSL_tile,
    setIntegral_Gamma1_fundDomain_PSL_eq_sum _
      (integrableOn_petersson_Gamma1_fundDomain_PSL f g)]

/-! ### Petersson inner product as an integral over a fundamental domain -/

/-- `petN f g` expressed as an integral over the canonical Γ₁(N)-fundamental
domain `Gamma1_fundDomain N`. -/
theorem petN_eq_setIntegral_Gamma1_fundDomain
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f g = (slToPslQuot_fiberCard N) •
      ∫ τ in Gamma1_fundDomain N, petersson k ⇑f ⇑g τ ∂μ_hyp :=
  petN_eq_setIntegral_Gamma1_fundDomain_PSL f g

/-- `petN f g` equals `(slToPslQuot_fiberCard N) • ∫_D petersson k f g` for *any*
`imageGamma1 N`-fundamental domain `D`. -/
theorem petN_eq_setIntegral_fundDomain
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {D : Set UpperHalfPlane}
    (hD : IsFundamentalDomain (imageGamma1 N) D μ_hyp) :
    petN f g = (slToPslQuot_fiberCard N) •
      ∫ τ in D, petersson k ⇑f ⇑g τ ∂μ_hyp := by
  rw [petN_eq_setIntegral_Gamma1_fundDomain_PSL,
    setIntegral_Gamma1_fundDomain_eq isFundamentalDomain_Gamma1_coset_tiling hD
      (petersson_imageGamma1_invariant f g)]

/-- For `α` in the normalizer of `imageGamma1 N`, `petN f g` equals the
(fiber-count weighted) integral of the Petersson integrand over the shifted
fundamental domain `α • Gamma1_fundDomain N`. -/
theorem petN_eq_setIntegral_normalizer_shift
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {α : PSL(2, ℤ)} (hα : α ∈ (imageGamma1 N).normalizer) :
    petN f g = (slToPslQuot_fiberCard N) •
      ∫ τ in α • Gamma1_fundDomain N, petersson k ⇑f ⇑g τ ∂μ_hyp :=
  petN_eq_setIntegral_fundDomain f g (isFundamentalDomain_Gamma1_shift hα)

/-- Per-tile reduction for `petN`-equalities: if the Petersson integrand
equalities hold tile-by-tile on the PSL fundamental domain, then
`petN`-equalities follow. -/
theorem petN_eq_of_per_tile_integral_eq
    (f₁ g₁ f₂ g₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_per_tile : ∀ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
      ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ),
        petersson k ⇑f₁ ⇑g₁ τ ∂μ_hyp =
      ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ),
        petersson k ⇑f₂ ⇑g₂ τ ∂μ_hyp) :
    petN f₁ g₁ = petN f₂ g₂ := by
  rw [petN_eq_nsmul_sum_PSL_tile f₁ g₁, petN_eq_nsmul_sum_PSL_tile f₂ g₂]
  congr 1
  exact Finset.sum_congr rfl fun q' _ ↦ h_per_tile q'

/-! ### Finite-family integration additivity for AE-disjoint covers -/

/-- For a finite family `s : ι → Set ℍ` of null-measurable, pairwise AE-disjoint
subsets of the upper half-plane, the integral of an integrable function over the
union equals the finite sum of integrals over each piece. -/
theorem setIntegral_iUnion_finite_aedisjoint
    {ι : Type*} [Fintype ι] (s : ι → Set ℍ)
    (hm : ∀ i, NullMeasurableSet (s i) μ_hyp)
    (hd : Pairwise (fun i j : ι ↦ AEDisjoint μ_hyp (s i) (s j)))
    (h : ℍ → ℂ) (hint : IntegrableOn h (⋃ i, s i) μ_hyp) :
    ∫ τ in ⋃ i : ι, s i, h τ ∂μ_hyp = ∑ i : ι, ∫ τ in s i, h τ ∂μ_hyp := by
  rw [integral_iUnion_ae hm hd hint, tsum_fintype]

/-- The Petersson-inner-product specialization of
`setIntegral_iUnion_finite_aedisjoint`: the inner product over a finite
AE-disjoint cover decomposes as the sum of inner products over each piece. -/
theorem peterssonInner_iUnion_finite_aedisjoint
    {ι : Type*} [Fintype ι] (s : ι → Set ℍ)
    (hm : ∀ i, NullMeasurableSet (s i) μ_hyp)
    (hd : Pairwise (fun i j : ι ↦ AEDisjoint μ_hyp (s i) (s j)))
    (f g : ℍ → ℂ)
    (hint : IntegrableOn (fun τ ↦ petersson k f g τ) (⋃ i, s i) μ_hyp) :
    peterssonInner k (⋃ i : ι, s i) f g =
      ∑ i : ι, peterssonInner k (s i) f g :=
  setIntegral_iUnion_finite_aedisjoint s hm hd _ hint

/-! ### Finite-family tile fundamental-domain bundle -/

/-- A finite-family tile fundamental-domain bundle: a `Fintype`-indexed
finite family `tile : ι → Set X` of pairwise AE-disjoint, null-measurable
subsets covering a target set `T` AE under a measure `μ`. -/
structure FiniteTileFundamentalDomain
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ι : Type*) [Fintype ι] (T : Set X) where
  /-- The finite tile family. -/
  tile : ι → Set X
  /-- Each tile is null-measurable. -/
  nullMeasurableSet_tile : ∀ i, NullMeasurableSet (tile i) μ
  /-- The target set is AE-covered by the tile union. -/
  aeCover : T =ᵐ[μ] ⋃ i, tile i
  /-- Tiles are pairwise AE-disjoint. -/
  pairwiseAEDisjoint :
    Pairwise (fun i j : ι ↦ AEDisjoint μ (tile i) (tile j))

namespace FiniteTileFundamentalDomain

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {ι : Type*} [Fintype ι] {T : Set X}

/-- The tile union (as an `abbrev` so it unfolds during type-checking). -/
abbrev union (F : FiniteTileFundamentalDomain μ ι T) : Set X := ⋃ i, F.tile i

/-- The tile union is null-measurable. -/
theorem nullMeasurableSet_union (F : FiniteTileFundamentalDomain μ ι T) :
    NullMeasurableSet F.union μ :=
  NullMeasurableSet.iUnion F.nullMeasurableSet_tile

/-- The target set is null-measurable (inherited from the tile union via
`aeCover`). -/
theorem nullMeasurableSet_target (F : FiniteTileFundamentalDomain μ ι T) :
    NullMeasurableSet T μ :=
  F.nullMeasurableSet_union.congr F.aeCover.symm

/-- **Integration consumer.** The integral over the target equals the
finite sum of integrals over each tile. -/
theorem setIntegral_eq_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : FiniteTileFundamentalDomain μ ι T) {f : X → E}
    (hint : IntegrableOn f F.union μ) :
    ∫ x in T, f x ∂μ = ∑ i : ι, ∫ x in F.tile i, f x ∂μ := by
  rw [setIntegral_congr_set F.aeCover,
    integral_iUnion_ae F.nullMeasurableSet_tile F.pairwiseAEDisjoint hint,
    tsum_fintype]

/-- **Measure additivity consumer.** The measure of the target equals the
finite sum of tile measures. -/
theorem measure_eq_sum (F : FiniteTileFundamentalDomain μ ι T) :
    μ T = ∑ i : ι, μ (F.tile i) := by
  rw [measure_congr F.aeCover,
    measure_iUnion₀ F.pairwiseAEDisjoint F.nullMeasurableSet_tile,
    tsum_fintype]

end FiniteTileFundamentalDomain

/-- The level-`N` Petersson inner product over a finite tile fundamental-domain
target decomposes as the finite sum of inner products over each tile. -/
theorem FiniteTileFundamentalDomain.peterssonInner_eq_sum
    {ι : Type*} [Fintype ι] {T : Set ℍ}
    (F : FiniteTileFundamentalDomain μ_hyp ι T)
    (f g : ℍ → ℂ)
    (hint : IntegrableOn (fun τ ↦ petersson k f g τ) F.union μ_hyp) :
    peterssonInner k T f g = ∑ i : ι, peterssonInner k (F.tile i) f g :=
  F.setIntegral_eq_sum hint

/-! ### Finite-family Petersson tile bridge from AE-equal unions -/

/-- Shifting the integration domain by an `SL₂(ℤ)` matrix `γ` is equivalent to
slashing both Petersson slots by `γ`:
`peterssonInner k (γ • S) f g = peterssonInner k S (f ∣[k] γ) (g ∣[k] γ)`. -/
theorem peterssonInner_smul_set_eq_slash
    (γ : SL(2, ℤ)) (S : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k ((γ : SL(2, ℤ)) • S) f g =
    peterssonInner k S (f ∣[k] (γ : SL(2, ℤ))) (g ∣[k] (γ : SL(2, ℤ))) := by
  unfold peterssonInner
  rw [setIntegral_smul_eq (fun τ ↦ petersson k f g τ) γ S]
  refine congrArg (fun (h : ℍ → ℂ) ↦ ∫ τ in S, h τ ∂μ_hyp) ?_
  funext τ
  exact (petersson_slash_SL k f g γ τ).symm

/-- If two subsets of `ℍ` are AE-equal under `μ_hyp`, integrability of the
Petersson kernel on one transfers to the other. -/
theorem integrableOn_petersson_congr_set_ae
    {S T : Set ℍ} (hST : S =ᵐ[μ_hyp] T)
    (f g : ℍ → ℂ) :
    IntegrableOn (fun τ ↦ petersson k f g τ) S μ_hyp ↔
    IntegrableOn (fun τ ↦ petersson k f g τ) T μ_hyp := by
  unfold IntegrableOn
  rw [Measure.restrict_congr_set hST]

/-- If two finite AE-disjoint families of null-measurable subsets of `ℍ` have
AE-equal unions, their Petersson-inner-product sum decompositions are equal. -/
theorem peterssonInner_sum_eq_of_AEDisjoint_unions_AEEq
    {ι₁ : Type*} [Fintype ι₁] (S₁ : ι₁ → Set ℍ)
    {ι₂ : Type*} [Fintype ι₂] (S₂ : ι₂ → Set ℍ)
    (hm₁ : ∀ i, NullMeasurableSet (S₁ i) μ_hyp)
    (hm₂ : ∀ j, NullMeasurableSet (S₂ j) μ_hyp)
    (hd₁ : Pairwise (fun i j : ι₁ ↦ AEDisjoint μ_hyp (S₁ i) (S₁ j)))
    (hd₂ : Pairwise (fun i j : ι₂ ↦ AEDisjoint μ_hyp (S₂ i) (S₂ j)))
    (h_union_eq : (⋃ i, S₁ i) =ᵐ[μ_hyp] (⋃ j, S₂ j))
    (f g : ℍ → ℂ)
    (hint : IntegrableOn (fun τ ↦ petersson k f g τ) (⋃ i, S₁ i) μ_hyp) :
    ∑ i : ι₁, peterssonInner k (S₁ i) f g =
    ∑ j : ι₂, peterssonInner k (S₂ j) f g := by
  rw [← peterssonInner_iUnion_finite_aedisjoint S₁ hm₁ hd₁ f g hint,
      ← peterssonInner_iUnion_finite_aedisjoint S₂ hm₂ hd₂ f g
        ((integrableOn_petersson_congr_set_ae h_union_eq f g).mp hint)]
  unfold peterssonInner
  exact setIntegral_congr_set h_union_eq

/-- Bundled form of `peterssonInner_sum_eq_of_AEDisjoint_unions_AEEq`: given two
`FiniteTileFundamentalDomain` bundles whose target sets are AE-equal under
`μ_hyp`, the Petersson-inner-product sums over their respective tile families
agree. -/
theorem FiniteTileFundamentalDomain.peterssonInner_sum_eq_of_target_aeEq
    {ι₁ : Type*} [Fintype ι₁] {T₁ : Set ℍ}
    (F₁ : FiniteTileFundamentalDomain μ_hyp ι₁ T₁)
    {ι₂ : Type*} [Fintype ι₂] {T₂ : Set ℍ}
    (F₂ : FiniteTileFundamentalDomain μ_hyp ι₂ T₂)
    (hT : T₁ =ᵐ[μ_hyp] T₂)
    (f g : ℍ → ℂ)
    (hint : IntegrableOn (fun τ ↦ petersson k f g τ) F₁.union μ_hyp) :
    ∑ i : ι₁, peterssonInner k (F₁.tile i) f g =
    ∑ j : ι₂, peterssonInner k (F₂.tile j) f g := by
  exact peterssonInner_sum_eq_of_AEDisjoint_unions_AEEq F₁.tile F₂.tile
    F₁.nullMeasurableSet_tile F₂.nullMeasurableSet_tile
    F₁.pairwiseAEDisjoint F₂.pairwiseAEDisjoint
    (F₁.aeCover.symm.trans (hT.trans F₂.aeCover)) f g hint

end
