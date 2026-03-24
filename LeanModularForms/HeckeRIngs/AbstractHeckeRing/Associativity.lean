/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Module

/-!
# Hecke Rings: Associativity

The `IsScalarTower` instance proving that the module action is compatible with multiplication,
which is equivalent to associativity of multiplication in the Hecke ring. This is Shimura
Proposition 3.4.
-/

open Commensurable Classical MulOpposite Set DoubleCoset Subgroup Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

open Finsupp

/-- IsScalarTower: `x •_M (y •_M z) = (y * x) •_M z` (Shimura Prop 3.4). -/
private lemma smulOrbit_map_injective (D : HeckeCoset P) (m₀ : HeckeLeftCoset P) :
    Function.Injective (fun i : decompQuot P (HeckeCoset.rep D) =>
      (⟦⟨((HeckeLeftCoset.rep m₀ : G) * (i.out : G) *
        (HeckeCoset.rep D : G)),
        delta_mul_mem P.H P.Δ i.out
          (HeckeLeftCoset.rep m₀) (HeckeCoset.rep D) P.h₀⟩⟧ : HeckeLeftCoset P)) := by
  intro i₁ i₂ heq
  by_contra hne
  have hset : ({(HeckeLeftCoset.rep m₀ : G) * (i₁.out : G) *
      (HeckeCoset.rep D : G)} : Set G) * (P.H : Set G) =
    {(HeckeLeftCoset.rep m₀ : G) * (i₂.out : G) *
      (HeckeCoset.rep D : G)} * P.H := Quotient.exact heq
  have hmem : (HeckeLeftCoset.rep m₀ : G) * (i₁.out : G) * (HeckeCoset.rep D : G) ∈
      ({(HeckeLeftCoset.rep m₀ : G) * (i₂.out : G) * (HeckeCoset.rep D : G)} : Set G) *
        (P.H : Set G) := by
    rw [← hset]; exact ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, ha, k, hk, hkk⟩ := hmem
  rw [Set.mem_singleton_iff] at ha; subst ha
  have cancel : (i₂.out : G) * (HeckeCoset.rep D : G) * k =
      (i₁.out : G) * (HeckeCoset.rep D : G) := by
    apply mul_left_cancel (a := (HeckeLeftCoset.rep m₀ : G))
    have := hkk; group at this ⊢; exact this
  apply decompQuot_coset_diff P (HeckeCoset.rep D) i₁ i₂ hne
  exact leftCoset_eq_of_not_disjoint (H := P.H) _ _ (by
    rw [@not_disjoint_iff]
    exact ⟨(i₁.out : G) * (HeckeCoset.rep D : G),
      ⟨1, P.H.one_mem, mul_one _⟩,
      ⟨k, hk, cancel⟩⟩)

private lemma smulOrbit_sum_eq (D : HeckeCoset P) (m₀ : HeckeLeftCoset P)
    (f : HeckeLeftCoset P → (HeckeLeftCoset P) →₀ ℤ) :
    ∑ i ∈ smulOrbit P D m₀, f i =
    ∑ q : decompQuot P (HeckeCoset.rep D), f
      (⟦⟨(HeckeLeftCoset.rep m₀ : G) * (q.out : G) * (HeckeCoset.rep D : G),
        delta_mul_mem P.H P.Δ q.out (HeckeLeftCoset.rep m₀)
          (HeckeCoset.rep D) P.h₀⟩⟧ : HeckeLeftCoset P) := by
  conv_lhs => rw [smulOrbit]; simp only [Finset.top_eq_univ]
  exact Finset.sum_image (fun a _ b _ hab => smulOrbit_map_injective P D m₀ hab)

private lemma smulOrbit_congr (D : HeckeCoset P) (m₁ m₂ : HeckeLeftCoset P)
    (h : m₁ = m₂) : smulOrbit P D m₁ = smulOrbit P D m₂ := h ▸ rfl

private lemma smulOrbit_sum_left_H_eq (D : HeckeCoset P) (β : P.Δ)
    (h : P.H) (c : ℤ) :
    ∑ q : decompQuot P (HeckeCoset.rep D), Finsupp.single
      (⟦⟨(β : G) * (h : G) * q.out *
        (HeckeCoset.rep D : G),
      Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ β.2 (P.h₀ h.2))
        (P.h₀ q.out.2)) (HeckeCoset.rep D).2⟩⟧ : HeckeLeftCoset P) c =
    ∑ q : decompQuot P (HeckeCoset.rep D), Finsupp.single
      (⟦⟨(β : G) * q.out * (HeckeCoset.rep D : G),
      delta_mul_mem P.H P.Δ q.out β (HeckeCoset.rep D) P.h₀⟩⟧ :
        HeckeLeftCoset P) c := by
  set g := (HeckeCoset.rep D : G) with hg_def
  set σ : decompQuot P (HeckeCoset.rep D) → decompQuot P (HeckeCoset.rep D) :=
    fun q => ⟦⟨(h : G) * q.out,
      P.H.mul_mem h.2 q.out.2⟩⟧
  have hσ : Function.Bijective σ := by
    constructor
    · intro q₁ q₂ heq
      simp only [σ] at heq
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at heq
      have hmem : (q₁.out : ↥P.H)⁻¹ * q₂.out ∈
          (ConjAct.toConjAct g • P.H).subgroupOf P.H := by
        convert heq using 1; ext; simp [Subgroup.coe_mul]; group
      rw [← @QuotientGroup.leftRel_apply, ← @Quotient.eq''] at hmem
      simp only [Quotient.out_eq'] at hmem
      exact hmem
    · intro q
      refine ⟨⟦⟨(h : G)⁻¹ * q.out, P.H.mul_mem (P.H.inv_mem h.2) q.out.2⟩⟧, ?_⟩
      simp only [σ]
      rw [← Quotient.out_eq q, @Quotient.eq'', QuotientGroup.leftRel_apply]
      have hout := Quotient.out_eq (s := QuotientGroup.leftRel _)
        (⟦⟨(h : G)⁻¹ * q.out, P.H.mul_mem (P.H.inv_mem h.2) q.out.2⟩⟧ :
          decompQuot P (HeckeCoset.rep D))
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hout
      convert hout using 1; ext; simp [Subgroup.coe_mul]; group
  have hval : ∀ q : decompQuot P (HeckeCoset.rep D),
      (⟦⟨(β : G) * (h : G) * q.out * g,
        Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ β.2 (P.h₀ h.2))
          (P.h₀ q.out.2)) (HeckeCoset.rep D).2⟩⟧ : HeckeLeftCoset P) =
      (⟦⟨(β : G) * (σ q).out * g,
        delta_mul_mem P.H P.Δ (σ q).out β (HeckeCoset.rep D) P.h₀⟩⟧ :
          HeckeLeftCoset P) := by
    intro q
    apply Quotient.sound
    show lcRel P _ _
    simp only [lcRel, σ]
    obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g • P.H).subgroupOf P.H) ⟨h * q.out, P.H.mul_mem h.2 q.out.2⟩
    have hn_coe : ((⟦⟨(h : G) * (q.out : G),
        P.H.mul_mem h.2 q.out.2⟩⟧ :
        decompQuot P (HeckeCoset.rep D)).out : G) =
        (h : G) * (q.out : G) * (n : G) := by
      have := congr_arg (Subtype.val : ↥P.H → G) hn_eq
      simpa [Subgroup.coe_mul] using this
    have hn_conj : g⁻¹ * (n : G) * g ∈ P.H := by
      have := n.2
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        ConjAct.smul_def] at this
      simpa [ConjAct.ofConjAct_toConjAct] using this
    ext x; constructor
    · rintro ⟨_, rfl, k, hk, rfl⟩
      exact ⟨_, rfl, (g⁻¹ * (n : G)⁻¹ * g) * k,
        P.H.mul_mem (by convert P.H.inv_mem hn_conj using 1; group) hk,
        by rw [hn_coe]; group⟩
    · rintro ⟨_, rfl, k, hk, rfl⟩
      exact ⟨_, rfl, (g⁻¹ * (n : G) * g) * k, P.H.mul_mem hn_conj hk,
        by rw [hn_coe]; group⟩
  exact Fintype.sum_bijective σ hσ _ _ (fun q => by congr 1; exact hval q)

private lemma conjAct_inv_mem_of_subgroupOf (g : G)
    (n : (ConjAct.toConjAct g • P.H).subgroupOf P.H) :
    g⁻¹ * (n : G)⁻¹ * g ∈ P.H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hn
  have := P.H.inv_mem hn; convert this using 1; group

private lemma conjAct_mem_of_subgroupOf (g : G)
    (n : (ConjAct.toConjAct g • P.H).subgroupOf P.H) :
    g⁻¹ * (n : G) * g ∈ P.H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simpa [ConjAct.ofConjAct_toConjAct] using hn

private lemma mk_out_coe_eq_mul {g : G} {h : P.H}
    {n : (ConjAct.toConjAct g • P.H).subgroupOf P.H}
    (hn_eq : (⟦h⟧ : P.H ⧸ (ConjAct.toConjAct g • P.H).subgroupOf P.H).out = h * n) :
    ((⟦h⟧ : P.H ⧸ (ConjAct.toConjAct g • P.H).subgroupOf P.H).out : G) =
      (h : G) * (n : G) := by
  have := congr_arg (Subtype.val : ↥P.H → G) hn_eq
  simpa [Subgroup.coe_mul] using this

private lemma decompQuot_eq_of_conjAct_rel (g : P.Δ)
    (i₁ i₂ : decompQuot P g)
    (h : (i₁.out : ↥P.H)⁻¹ * i₂.out ∈
      (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H) :
    i₁ = i₂ := by
  rw [← @QuotientGroup.leftRel_apply, ← @Quotient.eq''] at h
  simp only [Quotient.out_eq'] at h; exact h

private lemma coset_shift_fwd (q a b a' b' g₁ g₂ g_D n₁ n₂ : G)
    (hcond : ({a * g₂ * (b * g₁)} : Set G) * ↑P.H = {q * g_D} * ↑P.H)
    (ha' : a' = q⁻¹ * a * n₁) (hb' : b' = g₂⁻¹ * n₁⁻¹ * g₂ * b * n₂)
    (hn₂_conj : g₁⁻¹ * n₂ * g₁ ∈ P.H) :
    ({a' * g₂ * (b' * g₁)} : Set G) * ↑P.H = {g_D} * ↑P.H := by
  subst ha' hb'
  apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
  refine ⟨q⁻¹ * a * n₁ * g₂ * (g₂⁻¹ * n₁⁻¹ * g₂ * b * n₂ * g₁),
    ⟨1, P.H.one_mem, by simp [smul_eq_mul]⟩, ?_⟩
  have hmem : a * g₂ * (b * g₁) ∈ ({q * g_D} : Set G) * ↑P.H := by
    rw [← hcond]; exact ⟨_, rfl, 1, P.H.one_mem, by group⟩
  obtain ⟨_, h_eq, h₀, hh₀, hprod⟩ := hmem
  simp only [Set.mem_singleton_iff] at h_eq; subst h_eq
  refine ⟨h₀ * (g₁⁻¹ * n₂ * g₁), P.H.mul_mem hh₀ hn₂_conj, ?_⟩
  simp only [smul_eq_mul]; symm
  calc q⁻¹ * a * n₁ * g₂ * (g₂⁻¹ * n₁⁻¹ * g₂ * b * n₂ * g₁)
      = q⁻¹ * (a * g₂ * (b * g₁)) * (g₁⁻¹ * n₂ * g₁) := by group
    _ = g_D * (h₀ * (g₁⁻¹ * n₂ * g₁)) := by
        have hprod' : q * g_D * h₀ = a * g₂ * (b * g₁) := hprod
        rw [← hprod']; group

private lemma coset_shift_inv (q a b a' b' g₁ g₂ g_D m₁ m₂ : G)
    (hcond : ({a' * g₂ * (b' * g₁)} : Set G) * ↑P.H = {g_D} * ↑P.H)
    (ha : a = q * a' * m₁) (hb : b = g₂⁻¹ * m₁⁻¹ * g₂ * b' * m₂)
    (hm₂_conj : g₁⁻¹ * m₂ * g₁ ∈ P.H) :
    ({a * g₂ * (b * g₁)} : Set G) * ↑P.H = {q * g_D} * ↑P.H := by
  apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
  refine ⟨a * g₂ * (b * g₁), ⟨1, P.H.one_mem, by simp [smul_eq_mul]⟩, ?_⟩
  have hmem : a' * g₂ * (b' * g₁) ∈ ({g_D} : Set G) * ↑P.H := by
    rw [← hcond]; exact ⟨_, rfl, 1, P.H.one_mem, by group⟩
  obtain ⟨_, hd_eq, h₀, hh₀, hprod⟩ := hmem
  simp only [Set.mem_singleton_iff] at hd_eq
  refine ⟨h₀ * (g₁⁻¹ * m₂ * g₁), P.H.mul_mem hh₀ hm₂_conj, ?_⟩
  simp only [smul_eq_mul]; symm
  calc a * g₂ * (b * g₁)
      = q * (a' * g₂ * (b' * g₁)) * (g₁⁻¹ * m₂ * g₁) := by subst ha hb; group
    _ = q * g_D * (h₀ * (g₁⁻¹ * m₂ * g₁)) := by subst hd_eq; rw [← hprod]; group

/-- Uniform distribution of multiplicities: the count of coset pairs `(i,j)` mapping
to a given left coset `q₀H` within double coset `D` is independent of the choice of `q₀`
(Shimura Proposition 3.4). -/
lemma heckeMultiplicity_uniform (g₂ g₁ : P.Δ) (D : HeckeCoset P)
    (q₀ : decompQuot P (HeckeCoset.rep D)) :
    Nat.card {p : decompQuot P g₂ × decompQuot P g₁ |
      ({(p.1.out : G) * (g₂ : G)} : Set G) *
      {(p.2.out : G) * (g₁ : G)} * P.H =
      {(q₀.out : G) * (HeckeCoset.rep D : G)} * (P.H : Set G)} =
    Nat.card {p : decompQuot P g₂ × decompQuot P g₁ |
      ({(p.1.out : G) * (g₂ : G)} : Set G) *
      {(p.2.out : G) * (g₁ : G)} * P.H =
      {(HeckeCoset.rep D : G)} * (P.H : Set G)} := by
  set g₁' := (g₁ : G) with hg₁_def
  set g₂' := (g₂ : G) with hg₂_def
  set g_D := (HeckeCoset.rep D : G) with hgD_def
  apply Nat.card_congr
  let get_n : decompQuot P g₂ → (ConjAct.toConjAct g₂' • P.H).subgroupOf P.H := fun i =>
    (QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g₂' • P.H).subgroupOf P.H)
      ⟨(q₀.out : G)⁻¹ * i.out, P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩).choose
  refine Equiv.ofBijective (fun ⟨⟨i, j⟩, (hcond : _ = _)⟩ =>
    let i' : decompQuot P g₂ :=
      ⟦⟨(q₀.out : G)⁻¹ * i.out,
        P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩⟧
    let n := get_n i
    let hn_conj : g₂'⁻¹ * (n : G)⁻¹ * g₂' ∈ P.H := conjAct_inv_mem_of_subgroupOf P g₂' n
    let h_n : G := g₂'⁻¹ * (n : G)⁻¹ * g₂'
    let j' : decompQuot P g₁ := ⟦⟨h_n * j.out, P.H.mul_mem hn_conj j.out.2⟩⟧
    (⟨⟨i', j'⟩, by
      show ({(i'.out : G) * g₂'} : Set G) * {(j'.out : G) * g₁'} * P.H = {g_D} * P.H
      rw [Set.singleton_mul_singleton]
      have hcond' : ({(i.out : G) * g₂' * ((j.out : G) * g₁')} : Set G) * ↑P.H =
          {(q₀.out : G) * g_D} * ↑P.H := by
        rw [← Set.singleton_mul_singleton]; exact hcond
      have hn_coe : (i'.out : G) = (q₀.out : G)⁻¹ * (i.out : G) * (n : G) :=
        mk_out_coe_eq_mul P (QuotientGroup.mk_out_eq_mul
          ((ConjAct.toConjAct g₂' • P.H).subgroupOf P.H)
          ⟨(q₀.out : G)⁻¹ * i.out,
            P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩).choose_spec
      obtain ⟨n', hn'_eq⟩ := QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct g₁' • P.H).subgroupOf P.H)
        ⟨h_n * j.out, P.H.mul_mem hn_conj j.out.2⟩
      exact coset_shift_fwd P (q₀.out : G) (i.out : G) (j.out : G) (i'.out : G)
        (j'.out : G) g₁' g₂' g_D (n : G) (n' : G) hcond' hn_coe
        (mk_out_coe_eq_mul P hn'_eq) (conjAct_mem_of_subgroupOf P g₁' n')
    ⟩ : {p : decompQuot P g₂ × decompQuot P g₁ |
      ({(p.1.out : G) * g₂'} : Set G) * {(p.2.out : G) * g₁'} * P.H =
      {g_D} * P.H})) ?_
  constructor
  · intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩ heq
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
    obtain ⟨hi, hj⟩ := heq
    have hi₁₂ : i₁ = i₂ := by
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hi
      exact decompQuot_eq_of_conjAct_rel P g₂ i₁ i₂
        (by convert hi using 1; ext; simp [Subgroup.coe_mul]; group)
    subst hi₁₂
    have hj₁₂ : j₁ = j₂ := by
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hj
      exact decompQuot_eq_of_conjAct_rel P g₁ j₁ j₂
        (by convert hj using 1; ext; simp [Subgroup.coe_mul]; group)
    subst hj₁₂; rfl
  · intro ⟨⟨i', j'⟩, (hcond'_tgt : _ = _)⟩
    let i₀ : decompQuot P g₂ :=
      ⟦⟨(q₀.out : G) * i'.out, P.H.mul_mem q₀.out.2 i'.out.2⟩⟧
    let n₀ := get_n i₀
    have hn₀_conj : g₂'⁻¹ * (n₀ : G) * g₂' ∈ P.H := conjAct_mem_of_subgroupOf P g₂' n₀
    let j₀ : decompQuot P g₁ := ⟦⟨g₂'⁻¹ * (n₀ : G) * g₂' * j'.out,
      P.H.mul_mem hn₀_conj j'.out.2⟩⟧
    obtain ⟨m_i, hmi_eq⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g₂' • P.H).subgroupOf P.H)
      ⟨(q₀.out : G) * i'.out, P.H.mul_mem q₀.out.2 i'.out.2⟩
    obtain ⟨m_j, hmj_eq⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g₁' • P.H).subgroupOf P.H)
      ⟨g₂'⁻¹ * (n₀ : G) * g₂' * j'.out, P.H.mul_mem hn₀_conj j'.out.2⟩
    have hmi_coe : (i₀.out : G) = (q₀.out : G) * (i'.out : G) * (m_i : G) :=
      mk_out_coe_eq_mul P hmi_eq
    have hmj_coe : (j₀.out : G) = g₂'⁻¹ * (n₀ : G) * g₂' * (j'.out : G) * (m_j : G) :=
      mk_out_coe_eq_mul P hmj_eq
    have h_quot_eq : (⟦⟨(q₀.out : G)⁻¹ * (i₀.out : G),
        P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩⟧ : decompQuot P g₂) = i' := by
      rw [show i' = ⟦i'.out⟧ from (Quotient.out_eq' i').symm, @Quotient.eq'',
        QuotientGroup.leftRel_apply]
      have h := Quotient.out_eq' i₀
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at h
      convert h using 1; ext; simp [Subgroup.coe_mul]; group
    have h_n₀_mi : (n₀ : G) = (m_i : G)⁻¹ := by
      have hn₀_spec := (QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct g₂' • P.H).subgroupOf P.H)
        ⟨(q₀.out : G)⁻¹ * i₀.out,
          P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩).choose_spec
      have hn₀_val : (i'.out : G) = (q₀.out : G)⁻¹ * (i₀.out : G) * (n₀ : G) := by
        have h1 := congr_arg (Subtype.val : ↥P.H → G) hn₀_spec
        simp only [Subgroup.coe_mul] at h1
        rwa [show ((⟦⟨(q₀.out : G)⁻¹ * (i₀.out : G),
          P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩⟧ : decompQuot P g₂).out : G) =
          (i'.out : G) from by congr 1; simp [h_quot_eq]] at h1
      have h1 : (i'.out : G) = (i'.out : G) * (m_i : G) * (n₀ : G) := by
        conv_lhs => rw [hn₀_val]; rw [hmi_coe]
        group
      have h2 : (m_i : G) * (n₀ : G) = 1 := by
        have := congr_arg ((i'.out : G)⁻¹ * ·) h1
        simp only [inv_mul_cancel] at this; group at this; exact this.symm
      exact eq_inv_of_mul_eq_one_right h2
    have hcond₀ : ({(i₀.out : G) * g₂'} : Set G) * {(j₀.out : G) * g₁'} * P.H =
        {(q₀.out : G) * g_D} * P.H := by
      rw [Set.singleton_mul_singleton]
      exact coset_shift_inv P (q₀.out : G) (i₀.out : G) (j₀.out : G) (i'.out : G)
        (j'.out : G) g₁' g₂' g_D (m_i : G) (m_j : G)
        (by rw [← Set.singleton_mul_singleton]; exact hcond'_tgt)
        hmi_coe (by rw [hmj_coe, h_n₀_mi]) (conjAct_mem_of_subgroupOf P g₁' m_j)
    refine ⟨⟨⟨i₀, j₀⟩, hcond₀⟩, ?_⟩
    apply Subtype.ext; simp only [Prod.mk.injEq]; exact ⟨h_quot_eq, by
      rw [show j' = ⟦j'.out⟧ from (Quotient.out_eq' j').symm, @Quotient.eq'',
        QuotientGroup.leftRel_apply]
      have h_j₀ := Quotient.out_eq' j₀
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at h_j₀
      convert h_j₀ using 1; ext; simp [Subgroup.coe_mul]; group; rfl⟩

private lemma iter_mem_smulOrbit_mulMap (g₂ g₁ : P.Δ) (m₀ : HeckeLeftCoset P)
    (i : decompQuot P g₂) (j : decompQuot P g₁) :
    (⟦⟨(HeckeLeftCoset.rep m₀ : G) * i.out * (g₂ : G) *
      j.out * (g₁ : G),
      Submonoid.mul_mem _ (Submonoid.mul_mem _
        (delta_mul_mem P.H P.Δ i.out (HeckeLeftCoset.rep m₀) g₂ P.h₀)
        (P.h₀ j.out.2)) g₁.2⟩⟧ : HeckeLeftCoset P) ∈
    smulOrbit P (mulMap P g₂ g₁ (i, j)) m₀ := by
  set D := mulMap P g₂ g₁ (i, j) with hD_def
  set g_D := (HeckeCoset.rep D : G) with hgD_def
  set α := (HeckeLeftCoset.rep m₀ : G)
  have h_in_doset : (i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G)) ∈
      DoubleCoset.doubleCoset g_D P.H P.H := by
    have h1 := HeckeCoset.toSet_eq_rep D
    rw [← h1]
    show (i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G)) ∈ HeckeCoset.toSet (mulMap P g₂ g₁ (i, j))
    simp only [mulMap, HeckeCoset.toSet_mk]
    exact DoubleCoset.mem_doubleCoset_self P.H P.H _
  rw [DoubleCoset.mem_doubleCoset] at h_in_doset
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := h_in_doset
  set r : decompQuot P (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct g_D • P.H).subgroupOf P.H) ⟨h₁, hh₁⟩
  have hn_coe : (r.out : G) = h₁ * (n : G) := by
    have := congr_arg (Subtype.val : ↥P.H → G) hn_eq
    simpa [Subgroup.coe_mul] using this
  have hn_conj : g_D⁻¹ * (n : G)⁻¹ * g_D ∈ P.H := by
    have hn := n.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at hn
    have hsimp : ConjAct.ofConjAct (ConjAct.toConjAct g_D)⁻¹ = g_D⁻¹ := by
      rw [map_inv, ConjAct.ofConjAct_toConjAct]
    rw [hsimp] at hn
    have := P.H.inv_mem hn; convert this using 1; group
  suffices hsuff : (⟦⟨α * (r.out : G) * g_D,
      delta_mul_mem P.H P.Δ r.out (HeckeLeftCoset.rep m₀) (HeckeCoset.rep D) P.h₀⟩⟧ :
        HeckeLeftCoset P) =
    (⟦⟨α * (i.out : G) * (g₂ : G) * (j.out : G) * (g₁ : G),
      Submonoid.mul_mem _ (Submonoid.mul_mem _
        (delta_mul_mem P.H P.Δ i.out (HeckeLeftCoset.rep m₀) g₂ P.h₀)
        (P.h₀ j.out.2)) g₁.2⟩⟧ : HeckeLeftCoset P) by
    rw [← hsuff]
    show _ ∈ smulOrbit P D m₀
    simp only [smulOrbit, Finset.mem_image]
    exact ⟨r, Finset.mem_univ _, rfl⟩
  apply Quotient.sound; show lcRel P _ _; simp only [lcRel]
  apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
  refine ⟨α * h₁ * g_D, ?_, ?_⟩
  · refine ⟨g_D⁻¹ * (n : G)⁻¹ * g_D, hn_conj, ?_⟩
    simp only [smul_eq_mul]; rw [hn_coe]; group
  · refine ⟨h₂⁻¹, P.H.inv_mem hh₂, ?_⟩
    simp only [smul_eq_mul]
    have hprod' : (i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G)) = h₁ * g_D * h₂ := hprod
    calc α * (i.out : G) * (g₂ : G) * (j.out : G) * (g₁ : G) * h₂⁻¹
        = α * ((i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G))) * h₂⁻¹ := by group
      _ = α * (h₁ * g_D * h₂) * h₂⁻¹ := by rw [hprod']
      _ = α * h₁ * g_D := by group

private lemma iter_smulOrbit_mem_mulSupport_smulOrbit
    (g₂ g₁ : P.Δ) (m₀ j x₀ : HeckeLeftCoset P)
    (hj : j ∈ smulOrbit P (⟦g₂⟧ : HeckeCoset P) m₀)
    (hx₀ : x₀ ∈ smulOrbit P (⟦g₁⟧ : HeckeCoset P) j) :
    ∃ D, D ∈ mulSupport P g₂ g₁ ∧ x₀ ∈ smulOrbit P D m₀ := by
  sorry

private lemma smulOrbit_indicator_eq_sum (D₁ : HeckeCoset P)
    (_m₀ : HeckeLeftCoset P) (x₀ : HeckeLeftCoset P) (β : P.Δ) :
    (if x₀ ∈ smulOrbit P D₁
      (⟦β⟧ : HeckeLeftCoset P) then (1 : ℤ) else 0) =
    ∑ k : decompQuot P (HeckeCoset.rep D₁),
      if (⟦⟨(β : G) * (k.out : G) * (HeckeCoset.rep D₁ : G),
      delta_mul_mem P.H P.Δ k.out β (HeckeCoset.rep D₁) P.h₀⟩⟧ :
        HeckeLeftCoset P) = x₀ then 1 else 0 := by
  sorry

private lemma smulOrbit_count_eq_m' (g₂ g₁ : P.Δ) (D₀ : HeckeCoset P)
    (m₀ x₀ : HeckeLeftCoset P)
    (hx₀ : x₀ ∈ smulOrbit P D₀ m₀) :
    (∑ j ∈ smulOrbit P (⟦g₂⟧ : HeckeCoset P) m₀,
      if x₀ ∈ smulOrbit P (⟦g₁⟧ : HeckeCoset P) j then (1 : ℤ) else 0) =
    (m P g₂ g₁) D₀ := by
  sorry

private lemma smul_assoc_key (g₁ g₂ : P.Δ) (m₀ : HeckeLeftCoset P) :
    ((m P g₂ g₁).sum fun D b₁ ↦
      ∑ i ∈ smulOrbit P D m₀, Finsupp.single i (b₁ * 1)) =
    (∑ j ∈ smulOrbit P (⟦g₂⟧ : HeckeCoset P) m₀,
      Finsupp.single j 1).sum
      fun m b₂ ↦ ∑ i ∈ smulOrbit P (⟦g₁⟧ : HeckeCoset P) m,
        Finsupp.single i (1 * b₂) := by
  simp only [mul_one, one_mul]
  ext x₀
  simp only [Finsupp.sum_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp_rw [Finset.sum_ite_eq']
  have h_rhs : (∑ j ∈ smulOrbit P (⟦g₂⟧ : HeckeCoset P) m₀, Finsupp.single j 1).sum
      (fun a₁ b ↦ if x₀ ∈ smulOrbit P (⟦g₁⟧ : HeckeCoset P) a₁ then b else (0 : ℤ)) =
      ∑ j ∈ smulOrbit P (⟦g₂⟧ : HeckeCoset P) m₀,
        if x₀ ∈ smulOrbit P (⟦g₁⟧ : HeckeCoset P) j then 1 else 0 := by
    rw [← Finsupp.sum_finset_sum_index
      (h_zero := fun a => by simp)
      (h_add := fun a b₁ b₂ => by split_ifs <;> simp [*])]
    congr 1; ext j
    exact Finsupp.sum_single_index (by simp)
  rw [h_rhs]
  by_cases h_ex : ∃ D₀ ∈ (m P g₂ g₁).support, x₀ ∈ smulOrbit P D₀ m₀
  · obtain ⟨D₀, hD₀, hx₀⟩ := h_ex
    have h_lhs : (m P g₂ g₁).sum (fun a₁ b ↦
        if x₀ ∈ smulOrbit P a₁ m₀ then b
        else (0 : ℤ)) = (m P g₂ g₁) D₀ := by
      rw [Finsupp.sum]
      rw [Finset.sum_eq_single D₀
        (fun D hD hne => if_neg (Finset.disjoint_left.mp
          (smulOrbit_disjoint_of_ne P D₀ D m₀ hne.symm) hx₀))
        (fun h => absurd hD₀ h)]
      exact if_pos hx₀
    rw [h_lhs]
    exact (smulOrbit_count_eq_m' P g₂ g₁ D₀ m₀ x₀ hx₀).symm
  · push_neg at h_ex
    have h_lhs : (m P g₂ g₁).sum (fun a₁ b ↦
        if x₀ ∈ smulOrbit P a₁ m₀ then b
        else (0 : ℤ)) = 0 := by
      rw [Finsupp.sum]
      exact Finset.sum_eq_zero (fun D hD => if_neg (h_ex D hD))
    rw [h_lhs]
    exact (Finset.sum_eq_zero fun j hj => by
      simp only [ite_eq_right_iff, one_ne_zero]
      intro hmem
      obtain ⟨D, hD, hD_mem⟩ :=
        iter_smulOrbit_mem_mulSupport_smulOrbit
          P g₂ g₁ m₀ j x₀ hj hmem
      exact absurd hD_mem (h_ex D hD)).symm

private lemma smul_assoc_singles (D₁ D₂ : HeckeCoset P) (a₁ a₂ : ℤ)
    (m₀ : HeckeLeftCoset P) (c₀ : ℤ) :
    (T_single P ℤ D₂ a₂ * T_single P ℤ D₁ a₁) •
      (HeckeLeftCoset_single P ℤ m₀ c₀) =
    T_single P ℤ D₁ a₁ •
      (T_single P ℤ D₂ a₂ • HeckeLeftCoset_single P ℤ m₀ c₀) := by
  rw [mul_singleton_𝕋, single_smul_single]
  simp only [smul_eq_sum, HeckeLeftCoset_single, T_single]
  have hsi : ∀ (D : HeckeCoset P) (b : ℤ),
      (Finsupp.single m₀ c₀).sum (fun m b₂ =>
        ∑ i ∈ smulOrbit P D m,
          Finsupp.single i (b * b₂)) =
      ∑ i ∈ smulOrbit P D m₀, Finsupp.single i (b * c₀) := by
    intro D b
    rw [Finsupp.sum_single_index (by
      simp [mul_zero, Finsupp.single_zero,
        Finset.sum_const_zero])]
  simp_rw [hsi]
  rw [Finsupp.sum_single_index (by simp [zero_mul, Finsupp.single_zero, Finset.sum_const_zero])]
  apply Finsupp.ext; intro x₀
  simp only [Finsupp.sum_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp_rw [Finset.sum_ite_eq']
  have h_rhs : (∑ j ∈ smulOrbit P D₂ m₀, Finsupp.single j (a₂ * c₀)).sum
      (fun a b ↦ if x₀ ∈ smulOrbit P D₁ a then a₁ * b else (0 : ℤ)) =
      ∑ j ∈ smulOrbit P D₂ m₀,
        if x₀ ∈ smulOrbit P D₁ j
        then a₁ * (a₂ * c₀) else 0 := by
    rw [← Finsupp.sum_finset_sum_index
      (h_zero := fun a => by simp)
      (h_add := fun a b₁ b₂ => by split_ifs <;> simp [*, mul_add])]
    congr 1; ext j
    exact Finsupp.sum_single_index (by simp)
  rw [h_rhs]
  have h_lhs : (a₂ • a₁ • m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁)).sum
      (fun D b₁ ↦ if x₀ ∈ smulOrbit P D m₀ then b₁ * c₀ else (0 : ℤ)) =
      (m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁)).sum
      (fun D b₁ ↦
        if x₀ ∈ smulOrbit P D m₀
        then a₂ * (a₁ * b₁) * c₀
        else (0 : ℤ)) := by
    rw [show a₂ • a₁ • m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) =
      a₂ • (a₁ • m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁)) from rfl]
    rw [Finsupp.sum_smul_index (fun i => by split_ifs <;> simp)]
    rw [Finsupp.sum_smul_index (fun i => by split_ifs <;> simp)]
  rw [h_lhs]
  have key := smul_assoc_key P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) m₀
  rw [show (⟦HeckeCoset.rep D₂⟧ : HeckeCoset P) = D₂ from Quotient.out_eq _,
      show (⟦HeckeCoset.rep D₁⟧ : HeckeCoset P) = D₁ from Quotient.out_eq _] at key
  simp only [mul_one, one_mul] at key
  have key_pt := congr_fun (congr_arg DFunLike.coe key) x₀
  simp only [Finsupp.sum_apply, Finsupp.finset_sum_apply, Finsupp.single_apply] at key_pt
  simp_rw [Finset.sum_ite_eq'] at key_pt
  simp_rw [show ∀ (D : HeckeCoset P) (b₁ : ℤ),
      (if x₀ ∈ smulOrbit P D m₀ then a₂ * (a₁ * b₁) * c₀ else 0) =
      a₁ * a₂ * c₀ * (if x₀ ∈ smulOrbit P D m₀ then b₁ else 0) from
    fun D b₁ => by split_ifs <;> ring]
  simp_rw [show ∀ (j : HeckeLeftCoset P),
      (if x₀ ∈ smulOrbit P D₁ j then a₁ * (a₂ * c₀) else 0) =
      a₁ * a₂ * c₀ * (if x₀ ∈ smulOrbit P D₁ j then 1 else 0) from
    fun j => by split_ifs <;> ring]
  simp_rw [← Finset.mul_sum, ← Finsupp.mul_sum]
  congr 1
  have h_rhs2 : (∑ j ∈ smulOrbit P D₂ m₀, Finsupp.single j 1).sum
      (fun a₁ b ↦ if x₀ ∈ smulOrbit P D₁ a₁ then b else (0 : ℤ)) =
      ∑ j ∈ smulOrbit P D₂ m₀, if x₀ ∈ smulOrbit P D₁ j then 1 else 0 := by
    rw [← Finsupp.sum_finset_sum_index
      (h_zero := fun a => by simp)
      (h_add := fun a b₁ b₂ => by split_ifs <;> simp [*])]
    congr 1; ext j
    exact Finsupp.sum_single_index (by simp)
  rwa [h_rhs2] at key_pt

/-- The module action satisfies the scalar tower property `(x * y) • z = y • (x • z)`,
which is equivalent to associativity of multiplication (Shimura Proposition 3.4). -/
noncomputable instance instIsScalarTower :
    IsScalarTower (𝕋 P ℤ) (𝕋 P ℤ) (HeckeModule P ℤ) where
  smul_assoc x y z := by
    simp only [smul_def]
    induction x using Finsupp.induction_linear with
    | zero => simp only [mul_zero, zero_smul_HeckeModule]
    | add x₁ x₂ ih₁ ih₂ =>
      rw [mul_add, smul_add_left, ih₁, ih₂, ← smul_add_left]
    | single D₁ a₁ =>
      induction y using Finsupp.induction_linear with
      | zero => simp only [zero_mul, zero_smul_HeckeModule, smul_zero_HeckeModule]
      | add y₁ y₂ ih₁ ih₂ =>
        rw [add_mul, smul_add_left, ih₁, ih₂, smul_add_left, smul_add_right]
      | single D₂ a₂ =>
        induction z using Finsupp.induction_linear with
        | zero => simp only [smul_zero_HeckeModule]
        | add z₁ z₂ ih₁ ih₂ =>
          rw [smul_add_right, smul_add_right, ih₁, ih₂, smul_add_right]
        | single m₀ c₀ =>
          exact smul_assoc_singles P D₁ D₂ a₁ a₂ m₀ c₀
