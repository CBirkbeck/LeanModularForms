/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeAction

/-!
# Hecke Operators as Endomorphisms of Modular Forms

Constructs the Hecke operator `T(D)` as an endomorphism of `ModularForm 𝒮ℒ k`,
proving holomorphicity, linearity, and boundedness at cusps.

## Main definitions

* `heckeOperator` — `T(D) : ModularForm 𝒮ℒ k → ModularForm 𝒮ℒ k`
* `heckeOperatorLinear` — `T(D)` as a ℂ-linear map
* `heckeOperator_comp` — composition corresponds to Hecke algebra multiplication

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4
-/

open Matrix Matrix.SpecialLinearGroup Subgroup.Commensurable Pointwise
open HeckeRing DoubleCoset HeckeRing.GLn HeckeRing.GL2
open scoped Pointwise ModularForm MatrixGroups UpperHalfPlane Manifold

namespace HeckeRing.GL2

/-- `𝒮ℒ` has determinant 1: all elements come from SL₂(ℤ). -/
instance : Subgroup.HasDetOne 𝒮ℒ where
  det_eq {γ} hγ := by
    simp only [MonoidHom.mem_range] at hγ
    obtain ⟨s, rfl⟩ := hγ
    exact det_mapGL s

section Holomorphicity

/-- The Hecke slash action preserves holomorphicity. -/
lemma heckeSlash_holomorphic (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeSlash k D f) :=
  MDifferentiable.sum fun _ _ => hf.slash k _

end Holomorphicity

section ModularFormConstructor

/-- `GL₂(ℚ)` maps cusps of `𝒮ℒ` to cusps: the Möbius action preserves `ℙ¹(ℚ)`. -/
lemma glMap_smul_isCusp (A : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (glMap A • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  rw [show glMap A • OnePoint.map (Rat.cast : ℚ → ℝ) q =
      OnePoint.map (Rat.cast : ℚ → ℝ) (A • q)
      from (OnePoint.map_smul (algebraMap ℚ ℝ) A q).symm]
  exact ⟨_, rfl⟩

/-- The Hecke slash action preserves boundedness at cusps. -/
lemma heckeSlash_bdd_at_cusps (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ModularForm 𝒮ℒ k)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsBoundedAt (heckeSlash k D f) k := by
  simp only [heckeSlash]
  apply Finset.sum_induction _ (fun g => c.IsBoundedAt g k) (fun _ _ ha hb => ha.add hb)
    ((0 : ModularForm 𝒮ℒ k).bdd_at_cusps' hc)
  intro i _
  exact OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' (glMap_smul_isCusp _ hc))

/-- The Hecke operator `T(D)` on modular forms, preserving slash invariance and holomorphicity. -/
noncomputable def heckeOperator (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ModularForm 𝒮ℒ k) :
    ModularForm 𝒮ℒ k where
  toSlashInvariantForm := heckeSlashInvariant k D f.toSlashInvariantForm
  holo' := heckeSlash_holomorphic k D f f.holo'
  bdd_at_cusps' hc := heckeSlash_bdd_at_cusps k D f hc

end ModularFormConstructor

section LinearMap

/-- Hecke slash of negation. -/
lemma heckeSlash_neg (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ) :
    heckeSlash k D (-f) = -heckeSlash k D f := by
  simp only [heckeSlash, SlashAction.neg_slash, Finset.sum_neg_distrib]

/-- The Hecke operator `T(D)` as a `ℂ`-linear map on modular forms. -/
noncomputable def heckeOperatorLinear (k : ℤ) (D : HeckeCoset (GL_pair 2)) :
    ModularForm 𝒮ℒ k →ₗ[ℂ] ModularForm 𝒮ℒ k where
  toFun := heckeOperator k D
  map_add' f g := by
    ext z
    change heckeSlash k D (↑(f + g)) z =
      (heckeOperator k D f + heckeOperator k D g) z
    simp only [ModularForm.add_apply]
    change heckeSlash k D (↑f + ↑g) z =
      heckeSlash k D (↑f) z + heckeSlash k D (↑g) z
    rw [heckeSlash_add]; rfl
  map_smul' c f := by
    ext z
    change heckeSlash k D (↑(c • f)) z = (c • heckeOperator k D f) z
    change heckeSlash k D (c • ↑f) z = c • heckeSlash k D (↑f) z
    rw [heckeSlash_smul]; rfl

end LinearMap

section FiberSum

/-- For each pair `(i,j)` with `mulMap(i,j) = D`, decompose `σᵢδ₁·σⱼδ₂ = h₁·δ_D·h₂`
    to get both the slash equality `f ∣[k] (σⱼδ₂·σᵢδ₁) = f ∣[k] tRep D q` and
    the right-coset condition `{σᵢδ₁}·{σⱼδ₂}·H = {q·δ_D}·H`. -/
private lemma slash_and_coset_of_mulMap_eq (k : ℤ) (D₁ D₂ D : HeckeCoset (GL_pair 2))
    (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    (p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
         decompQuot (GL_pair 2) (HeckeCoset.rep D₂))
    (hp : mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D) :
    ∃ q : decompQuot (GL_pair 2) (HeckeCoset.rep D),
      (f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1) = f ∣[k] tRep D q) ∧
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) := by
  have hmem : (p.1.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈ HeckeCoset.toSet D := by
    have : HeckeCoset.toSet (mulMap (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2)) = HeckeCoset.toSet D := by rw [hp]
    rw [← this]
    show _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset (GL_pair 2))
    simp only [HeckeCoset.toSet_mk]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hmem
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hmem
  set q : decompQuot (GL_pair 2) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧; refine ⟨q, ?_, ?_⟩
  · rw [tRep_mul_anti D₁ D₂ p.1 p.2, heq]; exact slash_tRep_of_mem k D _ h₂ hh₁ hh₂ f hf
  · have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact (Quotient.out_eq q))
    rw [Subgroup.mem_subgroupOf] at h_K
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] at h_K
    simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at h_K
    set κ := (HeckeCoset.rep D : GL _ ℚ)⁻¹ * ((q.out : GL _ ℚ)⁻¹ * h₁) *
        (HeckeCoset.rep D : GL _ ℚ)
    rw [Set.singleton_mul_singleton, heq]; apply leftCoset_eq_of_not_disjoint
    rw [Set.not_disjoint_iff]
    exact ⟨h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂,
      ⟨1, (GL_pair 2).H.one_mem, by simp [smul_eq_mul]⟩,
      ⟨κ * h₂, (GL_pair 2).H.mul_mem h_K hh₂, by simp only [smul_eq_mul, κ]; group⟩⟩

/-- The product `σᵢδ₁ · σⱼδ₂` lies in `toSet D` when a right-coset witness exists. -/
private lemma prod_mem_D_of_rightCoset (D : HeckeCoset (GL_pair 2)) (g : GL (Fin 2) ℚ)
    (q : decompQuot (GL_pair 2) (HeckeCoset.rep D)) (h : GL (Fin 2) ℚ)
    (hh : h ∈ ((GL_pair 2).H : Set (GL (Fin 2) ℚ)))
    (hprod : g = (q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ) * h) :
    g ∈ HeckeCoset.toSet D := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  exact ⟨(q.out : GL (Fin 2) ℚ), SetLike.coe_mem q.out, h, hh, hprod⟩

/-- The product `σᵢδ₁ · σⱼδ₂` lies in `toSet (mulMap p)`. -/
private lemma prod_mem_mulMap (D₁ D₂ : HeckeCoset (GL_pair 2))
    (p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
         decompQuot (GL_pair 2) (HeckeCoset.rep D₂)) :
    (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      HeckeCoset.toSet (mulMap (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2)) := by
  show _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset (GL_pair 2))
  simp only [HeckeCoset.toSet_mk]; exact DoubleCoset.mem_doubleCoset_self _ _ _

/-- From a right-coset condition `{σᵢδ₁}·{σⱼδ₂}·H = {q·δ_D}·H`, derive
    that `mulMap(p) = D`: the product lands in the double coset `D`. -/
private lemma mulMap_eq_of_rightCoset (D₁ D₂ D : HeckeCoset (GL_pair 2))
    (p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
         decompQuot (GL_pair 2) (HeckeCoset.rep D₂))
    (q : decompQuot (GL_pair 2) (HeckeCoset.rep D))
    (hp_rc : ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ))) :
    mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D := by
  have h_in_rc : (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      ({(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} : Set _) *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) := by
    rw [← hp_rc, Set.singleton_mul_singleton]
    exact ⟨_, rfl, 1, (GL_pair 2).H.one_mem, by simp only [mul_one]⟩
  obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_in_rc
  rw [Set.mem_singleton_iff] at hd_eq; subst hd_eq
  set M := mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2)
  exact HeckeCoset_ext_toSet (GL_pair 2) (by
    rw [HeckeCoset.toSet_eq_rep, HeckeCoset.toSet_eq_rep]
    exact DoubleCoset.eq_of_not_disjoint (by
      rw [Set.not_disjoint_iff]
      have hm := prod_mem_mulMap D₁ D₂ p
      rw [HeckeCoset.toSet_eq_rep] at hm
      have hd := prod_mem_D_of_rightCoset D _ q h hh hprod.symm
      rw [HeckeCoset.toSet_eq_rep] at hd
      exact ⟨_, hm, hd⟩))

private lemma heckeSlash_fiber_sum [DecidableEq (HeckeCoset (GL_pair 2))] (k : ℤ)
    (D₁ D₂ D : HeckeCoset (GL_pair 2))
    (_hD : D ∈ mulSupport (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂))
    (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    (∑ p ∈ Finset.univ.filter
        (fun p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
                 decompQuot (GL_pair 2) (HeckeCoset.rep D₂) =>
          mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D),
      f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1)) =
    (m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D •
      ∑ q : decompQuot (GL_pair 2) (HeckeCoset.rep D),
        f ∣[k] tRep D q := by
  classical
  have h_main := slash_and_coset_of_mulMap_eq k D₁ D₂ D f hf
  set q_of : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
      decompQuot (GL_pair 2) (HeckeCoset.rep D₂) →
      decompQuot (GL_pair 2) (HeckeCoset.rep D) := fun p =>
    if h : mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D
    then (h_main p h).choose else ⟦1⟧
  have h_slash_eq : ∀ p,
      mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D →
      f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1) = f ∣[k] tRep D (q_of p) := by
    intro p hp; simp only [q_of, hp, dif_pos]; exact (h_main p hp).choose_spec.1
  have h_coset_eq : ∀ p,
      mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D →
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
      {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) := by
    intro p hp; simp only [q_of, hp, dif_pos]; exact (h_main p hp).choose_spec.2
  set S := Finset.univ.filter (fun p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
      decompQuot (GL_pair 2) (HeckeCoset.rep D₂) =>
      mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D)
  rw [Finset.sum_congr rfl (fun p hp => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact h_slash_eq p hp)]
  rw [← Finset.sum_fiberwise (s := S) (g := q_of)]
  conv_lhs =>
    arg 2; ext q
    rw [Finset.sum_congr rfl (fun p hp => by
      simp only [Finset.mem_filter] at hp; rw [hp.2])]
    rw [Finset.sum_const]
  have h_fiber_eq : ∀ q : decompQuot (GL_pair 2) (HeckeCoset.rep D),
      (S.filter (fun p => q_of p = q)).card = Nat.card
        {p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
             decompQuot (GL_pair 2) (HeckeCoset.rep D₂) |
          ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
          {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
          ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
          {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
          ((GL_pair 2).H : Set (GL (Fin 2) ℚ))} := by
    intro q; rw [← Nat.card_eq_finsetCard]; apply Nat.card_congr
    exact {
      toFun := fun ⟨p, hp⟩ => ⟨p, by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rw [← hp.2]; exact h_coset_eq p hp.1⟩
      invFun := fun ⟨p, hp_rc⟩ => ⟨p, by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        have hmap := mulMap_eq_of_rightCoset D₁ D₂ D p q hp_rc
        refine ⟨hmap, ?_⟩; simp only [q_of, hmap, dif_pos]
        set q' := (h_main p hmap).choose; by_contra hne
        exact decompQuot_coset_diff (GL_pair 2) (HeckeCoset.rep D) q' q hne
          ((h_main p hmap).choose_spec.2.symm.trans hp_rc)⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  simp_rw [h_fiber_eq,
    heckeMultiplicity_uniform (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) D]
  set n := Nat.card
    {p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
         decompQuot (GL_pair 2) (HeckeCoset.rep D₂) |
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
      {(HeckeCoset.rep D : GL _ ℚ)} * ((GL_pair 2).H : Set (GL (Fin 2) ℚ))}
  rw [show ∑ x : decompQuot (GL_pair 2) (HeckeCoset.rep D), n • f ∣[k] tRep D x =
      n • ∑ x, f ∣[k] tRep D x from Finset.sum_nsmul _ _ _]
  simp only [m, Finsupp.coe_mk, heckeMultiplicity, n, Nat.cast_smul_eq_nsmul ℤ]

end FiberSum

section HeckeAlgebraAction

/-- The extended Hecke slash action: extends `heckeSlash` by ℤ-linearity from single
    double cosets `HeckeCoset` to formal sums `𝕋 (GL_pair 2) ℤ` (the full Hecke algebra).
    `heckeSlashExt k T f = T.sum (fun D c => c • heckeSlash k D f)`. -/
noncomputable def heckeSlashExt (k : ℤ) (T : HeckeAlgebra 2) (f : ℍ → ℂ) : ℍ → ℂ :=
  T.sum (fun D c => c • heckeSlash k D f)

/-- The extended action on a single double coset recovers `heckeSlash`. -/
lemma heckeSlashExt_single (k : ℤ) (D : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ) :
    heckeSlashExt k (Finsupp.single D 1) f = heckeSlash k D f := by
  simp [heckeSlashExt, Finsupp.sum_single_index]

/-- Multiplicativity of the Hecke slash for Γ-invariant functions:
    `T(D₁)(T(D₂)(f)) = (T(D₂) * T(D₁))(f)` where `f` is any Γ-invariant function.
    The proof reindexes the double sum by grouping pairs `(i,j)` according to
    `mulMap(i,j)`, using `heckeMultiplicity_uniform` for the fiber counting. -/
private theorem heckeSlash_comp (k : ℤ) (D₁ D₂ : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) : heckeSlash k D₁ (heckeSlash k D₂ f) =
    heckeSlashExt k (T_single (GL_pair 2) ℤ D₂ 1 * T_single (GL_pair 2) ℤ D₁ 1) f := by
  rw [show heckeSlashExt k (T_single (GL_pair 2) ℤ D₂ 1 *
      T_single (GL_pair 2) ℤ D₁ 1) f =
      (m (GL_pair 2) (HeckeCoset.rep D₂) (HeckeCoset.rep D₁)).sum
        (fun D c => c • heckeSlash k D f) from by
    unfold heckeSlashExt; rw [mul_singleton_𝕋]; simp]
  have h_comm : m (GL_pair 2) (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) =
      m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) := by
    simpa only [T_single_one_mul_T_single_one] using
      mul_comm (T_single (GL_pair 2) ℤ D₂ 1) (T_single (GL_pair 2) ℤ D₁ 1)
  rw [h_comm]; simp_rw [heckeSlash]
  rw [show (∑ i : decompQuot (GL_pair 2) (HeckeCoset.rep D₁),
      (∑ j : decompQuot (GL_pair 2) (HeckeCoset.rep D₂),
        f ∣[k] tRep D₂ j) ∣[k] tRep D₁ i) =
      ∑ i, ∑ j, (f ∣[k] tRep D₂ j) ∣[k] tRep D₁ i from by
    congr 1; ext i
    induction Finset.univ (α := decompQuot (GL_pair 2) (HeckeCoset.rep D₂))
        using Finset.cons_induction with
    | empty => simp [SlashAction.zero_slash]
    | cons a s has ih => simp [Finset.sum_cons, SlashAction.add_slash]]
  have h_slash_mul :
      ∀ (i : decompQuot (GL_pair 2) (HeckeCoset.rep D₁))
        (j : decompQuot (GL_pair 2) (HeckeCoset.rep D₂)),
      (f ∣[k] tRep D₂ j) ∣[k] tRep D₁ i = f ∣[k] (tRep D₂ j * tRep D₁ i) := by
    intro i j
    show (f ∣[k] glMap (tRep D₂ j)) ∣[k] glMap (tRep D₁ i) =
      f ∣[k] glMap (tRep D₂ j * tRep D₁ i)
    rw [map_mul, ← SlashAction.slash_mul]
  simp_rw [h_slash_mul]; rw [← Fintype.sum_prod_type']
  change (∑ p : decompQuot (GL_pair 2) (HeckeCoset.rep D₁) ×
      decompQuot (GL_pair 2) (HeckeCoset.rep D₂),
      f ∣[k] (tRep D₂ p.2 * tRep D₁ p.1)) = _
  letI : DecidableEq (HeckeCoset (GL_pair 2)) := Classical.decEq _
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun p => mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2))
    (fun p _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)),
    show Finset.image (mulMap (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂))
      Finset.univ =
      mulSupport (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) from rfl,
    Finsupp.sum,
    show (m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)).support =
      mulSupport (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) from rfl]
  exact Finset.sum_congr rfl fun D hD => heckeSlash_fiber_sum k D₁ D₂ D hD f hf

end HeckeAlgebraAction

section Composition

/-- Composing Hecke operators corresponds to Hecke algebra multiplication
    (Shimura Proposition 3.30): `T(D₁)(T(D₂)(f)) = (T(D₂) · T(D₁))(f)`. -/
theorem heckeOperator_comp (k : ℤ) (D₁ D₂ : HeckeCoset (GL_pair 2)) (f : ModularForm 𝒮ℒ k) :
    (heckeOperator k D₁ (heckeOperator k D₂ f) : ℍ → ℂ) =
    heckeSlashExt k (T_single (GL_pair 2) ℤ D₂ 1 * T_single (GL_pair 2) ℤ D₁ 1) f :=
  heckeSlash_comp k D₁ D₂ f (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)

end Composition

section RingHom

/-! ### The Hecke algebra as endomorphisms of modular forms

Packages `heckeOperatorLinear` into a ring homomorphism
`𝕋 (GL_pair 2) ℤ →+* Module.End ℂ (ModularForm 𝒮ℒ k)`.

Composition of Hecke operators corresponds to `T(D₂) * T(D₁)` in the Hecke ring (Shimura
Prop 3.30). Since `𝕋 (GL_pair 2) ℤ` is commutative (Shimura Prop 3.8, via the transpose
anti-involution), this ordering ambiguity is irrelevant and we obtain a genuine
homomorphism rather than an anti-homomorphism. -/

open HeckeRing (T_single)

/-- The `ℂ`-linear endomorphism of modular forms attached to a Hecke algebra element
`T : 𝕋 (GL_pair 2) ℤ`, obtained by extending `heckeOperatorLinear` by `ℤ`-linearity. -/
noncomputable def heckeSum (k : ℤ) (T : HeckeAlgebra 2) :
    Module.End ℂ (ModularForm 𝒮ℒ k) :=
  T.sum (fun D c => c • heckeOperatorLinear k D)

@[simp] lemma heckeSum_zero (k : ℤ) : heckeSum k (0 : HeckeAlgebra 2) = 0 :=
  Finsupp.sum_zero_index

@[simp] lemma heckeSum_T_single (k : ℤ) (D : HeckeCoset (GL_pair 2)) (c : ℤ) :
    heckeSum k (T_single (GL_pair 2) ℤ D c) = c • heckeOperatorLinear k D :=
  Finsupp.sum_single_index (by simp)

lemma heckeSum_add (k : ℤ) (T₁ T₂ : HeckeAlgebra 2) :
    heckeSum k (T₁ + T₂) = heckeSum k T₁ + heckeSum k T₂ :=
  Finsupp.sum_add_index' (h_zero := fun _ => by simp)
    (h_add := fun _ c₁ c₂ => by rw [add_zsmul])

/-- Pointwise agreement of `heckeSum k T f` and `heckeSlashExt k T f` for each `z ∈ ℍ`. -/
lemma heckeSum_apply_apply (k : ℤ) (T : HeckeAlgebra 2) (f : ModularForm 𝒮ℒ k) (z : ℍ) :
    (heckeSum k T f) z = heckeSlashExt k T (f : ℍ → ℂ) z := by
  classical
  induction T using Finsupp.induction_linear with
  | zero =>
    simp only [heckeSum_zero, LinearMap.zero_apply, ModularForm.zero_apply]
    unfold heckeSlashExt
    rw [Finsupp.sum_zero_index]; rfl
  | add T₁ T₂ h₁ h₂ =>
    rw [heckeSum_add]
    simp only [LinearMap.add_apply, ModularForm.add_apply, h₁, h₂]
    unfold heckeSlashExt
    rw [show (T₁ + T₂).sum (fun D c => c • heckeSlash k D (f : ℍ → ℂ)) =
        T₁.sum (fun D c => c • heckeSlash k D (f : ℍ → ℂ)) +
        T₂.sum (fun D c => c • heckeSlash k D (f : ℍ → ℂ)) from
      Finsupp.sum_add_index' (h_zero := fun _ => by simp)
        (h_add := fun _ c₁ c₂ => by rw [add_zsmul])]
    rfl
  | single D c =>
    show (heckeSum k (T_single (GL_pair 2) ℤ D c) f) z = _
    rw [heckeSum_T_single]
    simp only [LinearMap.smul_apply, ModularForm.smul_apply]
    unfold heckeSlashExt
    rw [Finsupp.sum_single_index (by simp : (0 : ℤ) • heckeSlash k D _ = _)]
    rfl

/-- The Hecke slash action of `HeckeCoset.one` on a Γ-invariant function is the identity.
The sum defining `heckeSlash` has a single term (the decomposition quotient is trivial)
that lies in `H`, hence fixes any Γ-invariant function. -/
private lemma heckeSlash_one (k : ℤ) (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    heckeSlash k (HeckeCoset.one (GL_pair 2)) f = f := by
  haveI : Subsingleton (decompQuot (GL_pair 2)
      (HeckeCoset.rep (HeckeCoset.one (GL_pair 2)))) :=
    subsingleton_decompQuot_T_one (GL_pair 2)
  haveI : Nonempty (decompQuot (GL_pair 2)
      (HeckeCoset.rep (HeckeCoset.one (GL_pair 2)))) :=
    one_in_decompQuot_T_one (GL_pair 2)
  haveI : Unique (decompQuot (GL_pair 2)
      (HeckeCoset.rep (HeckeCoset.one (GL_pair 2)))) := uniqueOfSubsingleton default
  unfold heckeSlash
  rw [show (Finset.univ : Finset (decompQuot (GL_pair 2)
        (HeckeCoset.rep (HeckeCoset.one (GL_pair 2))))) = {default} from by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_univ _, fun i _ => Subsingleton.elim _ _⟩,
    Finset.sum_singleton]
  -- tRep = transpose of q.out * rep(one); this is an H-element transpose
  set q : decompQuot (GL_pair 2) (HeckeCoset.rep (HeckeCoset.one (GL_pair 2))) := default
  have hmem_H : (q.out : GL (Fin 2) ℚ) *
      (HeckeCoset.rep (HeckeCoset.one (GL_pair 2)) : GL (Fin 2) ℚ) ∈ (GL_pair 2).H :=
    (GL_pair 2).H.mul_mem (SetLike.coe_mem _) (HeckeCoset.one_rep_mem_H _)
  -- tRep(one) q is the transpose of h = q.out * rep(one), which is in H.
  -- Its transpose (an element of H via GL_transpose_mem_SLnZ) fixes f via Γ-invariance.
  show f ∣[k] tRep (HeckeCoset.one (GL_pair 2)) q = f
  have htr_mem : (GL_transposeEquiv 2
      ((q.out : GL (Fin 2) ℚ) *
        (HeckeCoset.rep (HeckeCoset.one (GL_pair 2)) : GL (Fin 2) ℚ))).unop ∈
      (GL_pair 2).H :=
    GL_transpose_mem_SLnZ 2 hmem_H
  show f ∣[k] glMap (tRep (HeckeCoset.one (GL_pair 2)) q) = f
  -- glMap of an H-element gives an element of 𝒮ℒ
  obtain ⟨s, hs⟩ := htr_mem
  have hmap : glMap (tRep (HeckeCoset.one (GL_pair 2)) q) = mapGL ℝ s := by
    have hrep : (tRep (HeckeCoset.one (GL_pair 2)) q : GL (Fin 2) ℚ) = mapGL ℚ s := by
      show ((GL_transposeEquiv 2 _).unop : GL (Fin 2) ℚ) = _
      rw [← hs]
    rw [hrep]; exact glMap_mapGL_eq s
  rw [hmap]
  exact hf _ (MonoidHom.mem_range.mpr ⟨s, rfl⟩)

/-- `heckeOperator k (HeckeCoset.one _) = id` on modular forms. -/
@[simp] lemma heckeOperator_one (k : ℤ) (f : ModularForm 𝒮ℒ k) :
    heckeOperator k (HeckeCoset.one (GL_pair 2)) f = f := by
  apply ModularForm.ext
  intro z
  change heckeSlash k (HeckeCoset.one (GL_pair 2)) (f : ℍ → ℂ) z = f z
  rw [heckeSlash_one k (f : ℍ → ℂ)
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)]

@[simp] lemma heckeOperatorLinear_one (k : ℤ) :
    heckeOperatorLinear k (HeckeCoset.one (GL_pair 2)) = 1 := by
  apply LinearMap.ext
  intro f
  show heckeOperator k (HeckeCoset.one (GL_pair 2)) f = (1 : Module.End ℂ _) f
  rw [Module.End.one_apply, heckeOperator_one]

@[simp] lemma heckeSum_one (k : ℤ) : heckeSum k (1 : HeckeAlgebra 2) = 1 := by
  rw [show (1 : HeckeAlgebra 2) = T_single (GL_pair 2) ℤ (HeckeCoset.one (GL_pair 2)) 1 from
    HeckeRing.one_def _ _, heckeSum_T_single, heckeOperatorLinear_one, one_smul]

/-- Helper: heckeSlashExt is `ℤ`-linear in the Hecke algebra argument. -/
private lemma heckeSlashExt_zsmul (k : ℤ) (n : ℤ) (T : HeckeAlgebra 2) (f : ℍ → ℂ) :
    heckeSlashExt k (n • T) f = n • heckeSlashExt k T f := by
  unfold heckeSlashExt
  rw [Finsupp.sum_smul_index (g := T) (b := n) (h := fun D c => c • heckeSlash k D f)
      (by simp), Finsupp.smul_sum]
  refine Finsupp.sum_congr ?_
  intro D _
  exact SemigroupAction.mul_smul _ _ _

/-- Helper: multiplicativity of `heckeSum` on basis elements. -/
private lemma heckeSum_mul_T_single (k : ℤ) (D₁ D₂ : HeckeCoset (GL_pair 2)) (a b : ℤ) :
    heckeSum k (T_single (GL_pair 2) ℤ D₁ a * T_single (GL_pair 2) ℤ D₂ b) =
      heckeSum k (T_single (GL_pair 2) ℤ D₁ a) *
        heckeSum k (T_single (GL_pair 2) ℤ D₂ b) := by
  -- Step 1: flip using commutativity of 𝕋 (GL_pair 2) ℤ
  rw [show T_single (GL_pair 2) ℤ D₁ a * T_single (GL_pair 2) ℤ D₂ b =
      T_single (GL_pair 2) ℤ D₂ b * T_single (GL_pair 2) ℤ D₁ a from mul_comm _ _]
  apply LinearMap.ext
  intro f
  apply ModularForm.ext
  intro z
  -- Step 2: convert LHS to underlying ℍ → ℂ
  rw [heckeSum_apply_apply]
  -- Step 3: expand T_single * T_single = (b*a) • (T_single 1 * T_single 1)
  have h_prod : T_single (GL_pair 2) ℤ D₂ b * T_single (GL_pair 2) ℤ D₁ a =
      (b * a) • (T_single (GL_pair 2) ℤ D₂ 1 * T_single (GL_pair 2) ℤ D₁ 1) := by
    rw [HeckeRing.T_single_mul_T_single, HeckeRing.T_single_mul_T_single,
      one_smul, one_smul, ← SemigroupAction.mul_smul]
  rw [h_prod, heckeSlashExt_zsmul]
  -- Now apply heckeOperator_comp
  rw [← heckeOperator_comp k D₁ D₂ f]
  -- Compute RHS
  show (b * a : ℤ) • (heckeOperator k D₁ (heckeOperator k D₂ f) : ℍ → ℂ) z =
      ((heckeSum k (T_single (GL_pair 2) ℤ D₁ a) *
        heckeSum k (T_single (GL_pair 2) ℤ D₂ b)) f) z
  rw [heckeSum_T_single, heckeSum_T_single]
  show (b * a : ℤ) • (heckeOperator k D₁ (heckeOperator k D₂ f) : ℍ → ℂ) z =
      (a • heckeOperatorLinear k D₁) ((b • heckeOperatorLinear k D₂) f) z
  simp only [LinearMap.smul_apply, ModularForm.smul_apply]
  rw [show (heckeOperatorLinear k D₁) (b • heckeOperatorLinear k D₂ f) =
      b • (heckeOperatorLinear k D₁) (heckeOperatorLinear k D₂ f) from
    (heckeOperatorLinear k D₁).map_smul_of_tower b _]
  rw [ModularForm.smul_apply]
  show (b * a : ℤ) • (heckeOperator k D₁ (heckeOperator k D₂ f) : ℍ → ℂ) z =
      a • b • (heckeOperator k D₁ (heckeOperator k D₂ f) : ℍ → ℂ) z
  rw [smul_smul, mul_comm b a]

lemma heckeSum_mul (k : ℤ) (T₁ T₂ : HeckeAlgebra 2) :
    heckeSum k (T₁ * T₂) = heckeSum k T₁ * heckeSum k T₂ := by
  induction T₁ using Finsupp.induction_linear with
  | zero => simp [zero_mul]
  | add T₁ T₁' h h' =>
    rw [add_mul, heckeSum_add, heckeSum_add, h, h', add_mul]
  | single D₁ a =>
    induction T₂ using Finsupp.induction_linear with
    | zero => simp [mul_zero]
    | add T₂ T₂' h h' =>
      rw [mul_add, heckeSum_add, heckeSum_add, h, h', mul_add]
    | single D₂ b => exact heckeSum_mul_T_single k D₁ D₂ a b

/-- The Hecke algebra as endomorphisms of modular forms (Shimura Prop 3.30). Maps a
formal sum `T = ∑ c_D · [D]` to `∑ c_D · T(D)`; multiplicativity comes from
`heckeOperator_comp` plus the commutativity of `𝕋 (GL_pair 2) ℤ`. -/
noncomputable def heckeRingHom (k : ℤ) :
    HeckeAlgebra 2 →+* Module.End ℂ (ModularForm 𝒮ℒ k) where
  toFun := heckeSum k
  map_zero' := heckeSum_zero k
  map_one' := heckeSum_one k
  map_add' := heckeSum_add k
  map_mul' := heckeSum_mul k

@[simp] lemma heckeRingHom_apply (k : ℤ) (T : HeckeAlgebra 2) :
    heckeRingHom k T = heckeSum k T := rfl

@[simp] lemma heckeRingHom_T_single (k : ℤ) (D : HeckeCoset (GL_pair 2)) (c : ℤ) :
    heckeRingHom k (T_single (GL_pair 2) ℤ D c) = c • heckeOperatorLinear k D :=
  heckeSum_T_single k D c

end RingHom

end HeckeRing.GL2
