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

## Main results

* `HeckeRing.heckeMultiplicity_uniform`: the number of coset pairs `(i, j)` mapping to a given
  left coset within a double coset is independent of the chosen representative.
* `HeckeRing.instIsScalarTower`: the scalar tower property `(x * y) • z = y • (x • z)`, which is
  equivalent to associativity of multiplication in the Hecke ring.
-/

open Commensurable Classical MulOpposite Set DoubleCoset Subgroup Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

open Finsupp

private lemma smulOrbit_map_injective (g β : P.Δ) :
    Function.Injective (fun i : decompQuot P g ↦
      (⟦⟨(β : G) * (i.out : G) * (g : G),
        delta_mul_mem P.H P.Δ i.out β g P.h₀⟩⟧ : HeckeLeftCoset P)) := by
  intro i₁ i₂ heq
  by_contra hne
  have hmem : (β : G) * (i₁.out : G) * (g : G) ∈
      ({(β : G) * (i₂.out : G) * (g : G)} : Set G) *
        (P.H : Set G) := by
    rw [← (Quotient.exact heq : ({(β : G) * (i₁.out : G) * (g : G)} : Set G) * (P.H : Set G) =
      {(β : G) * (i₂.out : G) * (g : G)} * P.H)]
    exact ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, ha, k, hk, hkk⟩ := hmem
  rw [Set.mem_singleton_iff] at ha
  subst ha
  have cancel : (i₂.out : G) * (g : G) * k = (i₁.out : G) * (g : G) := by
    apply mul_left_cancel (a := (β : G))
    group at hkk ⊢
    exact hkk
  apply decompQuot_coset_diff P g i₁ i₂ hne
  refine leftCoset_eq_of_not_disjoint (H := P.H) _ _ ?_
  rw [not_disjoint_iff]
  exact ⟨(i₁.out : G) * (g : G), ⟨1, P.H.one_mem, mul_one _⟩, ⟨k, hk, cancel⟩⟩

private lemma smulOrbit_sum_eq (g β : P.Δ) (f : HeckeLeftCoset P → (HeckeLeftCoset P) →₀ ℤ) :
    ∑ i ∈ smulOrbit P g β, f i =
    ∑ q : decompQuot P g, f
      (⟦⟨(β : G) * (q.out : G) * (g : G),
        delta_mul_mem P.H P.Δ q.out β g P.h₀⟩⟧ : HeckeLeftCoset P) := by
  conv_lhs => rw [smulOrbit]; simp only [Finset.top_eq_univ]
  exact Finset.sum_image fun a _ b _ hab ↦ smulOrbit_map_injective P g β hab

private lemma decompQuot_leftMul_bijective (g₀ : P.Δ) (h : P.H) :
    Function.Bijective (fun q : decompQuot P g₀ ↦
      (⟦⟨(h : G) * q.out, P.H.mul_mem h.2 q.out.2⟩⟧ : decompQuot P g₀)) := by
  constructor
  · intro q₁ q₂ heq
    rw [Quotient.eq'', QuotientGroup.leftRel_apply] at heq
    have hmem : (q₁.out : ↥P.H)⁻¹ * q₂.out ∈
        (ConjAct.toConjAct (g₀ : G) • P.H).subgroupOf P.H := by
      convert heq using 1
      ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev]
      group
    rw [← QuotientGroup.leftRel_apply, ← Quotient.eq''] at hmem
    simpa using hmem
  · intro q
    refine ⟨⟦⟨(h : G)⁻¹ * q.out, P.H.mul_mem (P.H.inv_mem h.2) q.out.2⟩⟧, ?_⟩
    rw [← Quotient.out_eq q, Quotient.eq'', QuotientGroup.leftRel_apply]
    have hout := Quotient.out_eq (s := QuotientGroup.leftRel _)
      (⟦⟨(h : G)⁻¹ * q.out, P.H.mul_mem (P.H.inv_mem h.2) q.out.2⟩⟧ :
        decompQuot P g₀)
    rw [Quotient.eq'', QuotientGroup.leftRel_apply] at hout
    convert hout using 1
    ext
    simp only [Quotient.out_eq, Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev]
    group

private lemma decompQuot_beta_leftMul_coset_eq (g₀ β : P.Δ) (h : P.H) (q : decompQuot P g₀) :
    (⟦⟨(β : G) * (h : G) * q.out * (g₀ : G),
        Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ β.2 (P.h₀ h.2))
          (P.h₀ q.out.2)) g₀.2⟩⟧ : HeckeLeftCoset P) =
      (⟦⟨(β : G) * (⟦⟨(h : G) * q.out, P.H.mul_mem h.2 q.out.2⟩⟧ :
          decompQuot P g₀).out * (g₀ : G),
        delta_mul_mem P.H P.Δ
          (⟦⟨(h : G) * q.out, P.H.mul_mem h.2 q.out.2⟩⟧ : decompQuot P g₀).out
          β g₀ P.h₀⟩⟧ : HeckeLeftCoset P) := by
  apply Quotient.sound
  change lcRel P _ _
  simp only [lcRel]
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g₀ : G) • P.H).subgroupOf P.H) ⟨h * q.out, P.H.mul_mem h.2 q.out.2⟩
  have hn_coe : ((⟦⟨(h : G) * (q.out : G),
      P.H.mul_mem h.2 q.out.2⟩⟧ :
      decompQuot P g₀).out : G) =
      (h : G) * (q.out : G) * (n : G) := by
    simpa [Subgroup.coe_mul] using congr_arg (Subtype.val : ↥P.H → G) hn_eq
  have hn_conj : (g₀ : G)⁻¹ * (n : G) * (g₀ : G) ∈ P.H := by
    have hn := n.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at hn
    simpa using hn
  ext x
  constructor
  · rintro ⟨_, rfl, k, hk, rfl⟩
    exact ⟨_, rfl, ((g₀ : G)⁻¹ * (n : G)⁻¹ * (g₀ : G)) * k,
      P.H.mul_mem (by convert P.H.inv_mem hn_conj using 1; group) hk,
      by rw [hn_coe]; group⟩
  · rintro ⟨_, rfl, k, hk, rfl⟩
    exact ⟨_, rfl, ((g₀ : G)⁻¹ * (n : G) * (g₀ : G)) * k, P.H.mul_mem hn_conj hk,
      by rw [hn_coe]; group⟩

private lemma smulOrbit_sum_left_H_eq (g₀ β : P.Δ) (h : P.H) (c : ℤ) :
    ∑ q : decompQuot P g₀, Finsupp.single
      (⟦⟨(β : G) * (h : G) * q.out * (g₀ : G),
      Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ β.2 (P.h₀ h.2))
        (P.h₀ q.out.2)) g₀.2⟩⟧ : HeckeLeftCoset P) c =
    ∑ q : decompQuot P g₀, Finsupp.single
      (⟦⟨(β : G) * q.out * (g₀ : G), delta_mul_mem P.H P.Δ q.out β g₀ P.h₀⟩⟧ :
        HeckeLeftCoset P) c := by
  set σ : decompQuot P g₀ → decompQuot P g₀ :=
    fun q ↦ ⟦⟨(h : G) * q.out, P.H.mul_mem h.2 q.out.2⟩⟧
  exact Fintype.sum_bijective σ (decompQuot_leftMul_bijective P g₀ h) _ _
    fun q ↦ by congr 1; exact decompQuot_beta_leftMul_coset_eq P g₀ β h q

private lemma conjAct_inv_mem_of_subgroupOf (g : G)
    (n : (ConjAct.toConjAct g • P.H).subgroupOf P.H) : g⁻¹ * (n : G)⁻¹ * g ∈ P.H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hn
  convert P.H.inv_mem hn using 1
  group

private lemma conjAct_mem_of_subgroupOf (g : G)
    (n : (ConjAct.toConjAct g • P.H).subgroupOf P.H) : g⁻¹ * (n : G) * g ∈ P.H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simpa using hn

private lemma mk_out_coe_eq_mul {g : G} {h : P.H}
    {n : (ConjAct.toConjAct g • P.H).subgroupOf P.H}
    (hn_eq : (⟦h⟧ : P.H ⧸ (ConjAct.toConjAct g • P.H).subgroupOf P.H).out = h * n) :
    ((⟦h⟧ : P.H ⧸ (ConjAct.toConjAct g • P.H).subgroupOf P.H).out : G) = (h : G) * (n : G) := by
  simpa using congr_arg (Subtype.val : ↥P.H → G) hn_eq

private lemma decompQuot_eq_of_conjAct_rel (g : P.Δ) (i₁ i₂ : decompQuot P g)
    (h : (i₁.out : ↥P.H)⁻¹ * i₂.out ∈ (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H) :
    i₁ = i₂ := by
  rw [← QuotientGroup.leftRel_apply, ← Quotient.eq''] at h
  simpa using h

private lemma coset_shift_fwd (q a b a' b' g₁ g₂ g_D n₁ n₂ : G)
    (hcond : ({a * g₂ * (b * g₁)} : Set G) * ↑P.H = {q * g_D} * ↑P.H)
    (ha' : a' = q⁻¹ * a * n₁) (hb' : b' = g₂⁻¹ * n₁⁻¹ * g₂ * b * n₂)
    (hn₂_conj : g₁⁻¹ * n₂ * g₁ ∈ P.H) :
    ({a' * g₂ * (b' * g₁)} : Set G) * ↑P.H = {g_D} * ↑P.H := by
  subst ha' hb'
  apply leftCoset_eq_of_not_disjoint
  rw [not_disjoint_iff]
  refine ⟨q⁻¹ * a * n₁ * g₂ * (g₂⁻¹ * n₁⁻¹ * g₂ * b * n₂ * g₁),
    ⟨1, P.H.one_mem, by simp⟩, ?_⟩
  have hmem : a * g₂ * (b * g₁) ∈ ({q * g_D} : Set G) * ↑P.H := by
    rw [← hcond]
    exact ⟨_, rfl, 1, P.H.one_mem, by group⟩
  obtain ⟨_, h_eq, h₀, hh₀, hprod⟩ := hmem
  simp only [Set.mem_singleton_iff] at h_eq
  subst h_eq
  refine ⟨h₀ * (g₁⁻¹ * n₂ * g₁), P.H.mul_mem hh₀ hn₂_conj, ?_⟩
  simp only [smul_eq_mul]
  symm
  calc q⁻¹ * a * n₁ * g₂ * (g₂⁻¹ * n₁⁻¹ * g₂ * b * n₂ * g₁)
      = q⁻¹ * (a * g₂ * (b * g₁)) * (g₁⁻¹ * n₂ * g₁) := by group
    _ = g_D * (h₀ * (g₁⁻¹ * n₂ * g₁)) := by rw [← hprod]; group

private lemma coset_shift_inv (q a b a' b' g₁ g₂ g_D m₁ m₂ : G)
    (hcond : ({a' * g₂ * (b' * g₁)} : Set G) * ↑P.H = {g_D} * ↑P.H)
    (ha : a = q * a' * m₁) (hb : b = g₂⁻¹ * m₁⁻¹ * g₂ * b' * m₂)
    (hm₂_conj : g₁⁻¹ * m₂ * g₁ ∈ P.H) :
    ({a * g₂ * (b * g₁)} : Set G) * ↑P.H = {q * g_D} * ↑P.H := by
  apply leftCoset_eq_of_not_disjoint
  rw [not_disjoint_iff]
  refine ⟨a * g₂ * (b * g₁), ⟨1, P.H.one_mem, by simp⟩, ?_⟩
  have hmem : a' * g₂ * (b' * g₁) ∈ ({g_D} : Set G) * ↑P.H := by
    rw [← hcond]
    exact ⟨_, rfl, 1, P.H.one_mem, by group⟩
  obtain ⟨_, hd_eq, h₀, hh₀, hprod⟩ := hmem
  simp only [Set.mem_singleton_iff] at hd_eq
  refine ⟨h₀ * (g₁⁻¹ * m₂ * g₁), P.H.mul_mem hh₀ hm₂_conj, ?_⟩
  simp only [smul_eq_mul]
  symm
  calc a * g₂ * (b * g₁)
      = q * (a' * g₂ * (b' * g₁)) * (g₁⁻¹ * m₂ * g₁) := by subst ha hb; group
    _ = q * g_D * (h₀ * (g₁⁻¹ * m₂ * g₁)) := by subst hd_eq; rw [← hprod]; group

private lemma representative_cancel_eq_inv (a m n : G) (h : a = a * m * n) : n = m⁻¹ :=
  eq_inv_of_mul_eq_one_right
    (mul_left_cancel (a := a) (by rw [mul_one, ← mul_assoc]; exact h.symm))

private noncomputable def uniformShiftElt (g₂ : P.Δ) (D : HeckeCoset P)
    (q₀ : decompQuot P (HeckeCoset.rep D)) (i : decompQuot P g₂) :
    (ConjAct.toConjAct (g₂ : G) • P.H).subgroupOf P.H :=
  (QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g₂ : G) • P.H).subgroupOf P.H)
    ⟨(q₀.out : G)⁻¹ * i.out, P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩).choose

private noncomputable def heckeMultiplicity_uniform_fwdMap (g₂ g₁ : P.Δ)
    (D : HeckeCoset P) (q₀ : decompQuot P (HeckeCoset.rep D))
    (p : {p : decompQuot P g₂ × decompQuot P g₁ |
      ({(p.1.out : G) * (g₂ : G)} : Set G) * {(p.2.out : G) * (g₁ : G)} * P.H =
      {(q₀.out : G) * (HeckeCoset.rep D : G)} * (P.H : Set G)}) :
    {p : decompQuot P g₂ × decompQuot P g₁ |
      ({(p.1.out : G) * (g₂ : G)} : Set G) * {(p.2.out : G) * (g₁ : G)} * P.H =
      {(HeckeCoset.rep D : G)} * (P.H : Set G)} :=
  let i := p.1.1
  let j := p.1.2
  let i' : decompQuot P g₂ :=
    ⟦⟨(q₀.out : G)⁻¹ * i.out, P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩⟧
  let n := uniformShiftElt P g₂ D q₀ i
  let hn_conj : (g₂ : G)⁻¹ * (n : G)⁻¹ * (g₂ : G) ∈ P.H :=
    conjAct_inv_mem_of_subgroupOf P (g₂ : G) n
  let j' : decompQuot P g₁ :=
    ⟦⟨(g₂ : G)⁻¹ * (n : G)⁻¹ * (g₂ : G) * j.out, P.H.mul_mem hn_conj j.out.2⟩⟧
  ⟨⟨i', j'⟩, by
    change ({(i'.out : G) * (g₂ : G)} : Set G) * {(j'.out : G) * (g₁ : G)} * P.H =
      {(HeckeCoset.rep D : G)} * P.H
    rw [Set.singleton_mul_singleton]
    have hcond' : ({(i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G))} : Set G) * ↑P.H =
        {(q₀.out : G) * (HeckeCoset.rep D : G)} * ↑P.H := by
      rw [← Set.singleton_mul_singleton]; exact p.2
    obtain ⟨n', hn'_eq⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct (g₁ : G) • P.H).subgroupOf P.H)
      ⟨(g₂ : G)⁻¹ * (n : G)⁻¹ * (g₂ : G) * j.out, P.H.mul_mem hn_conj j.out.2⟩
    exact coset_shift_fwd P (q₀.out : G) (i.out : G) (j.out : G) (i'.out : G)
      (j'.out : G) (g₁ : G) (g₂ : G) (HeckeCoset.rep D : G) (n : G) (n' : G) hcond'
      (mk_out_coe_eq_mul P (QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct (g₂ : G) • P.H).subgroupOf P.H)
        ⟨(q₀.out : G)⁻¹ * i.out,
          P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩).choose_spec)
      (mk_out_coe_eq_mul P hn'_eq) (conjAct_mem_of_subgroupOf P (g₁ : G) n')⟩

private lemma uniformShiftElt_eq_m_inv (g₂ : P.Δ) (D : HeckeCoset P)
    (q₀ : decompQuot P (HeckeCoset.rep D)) (i' i₀ : decompQuot P g₂)
    (m_i : (ConjAct.toConjAct (g₂ : G) • P.H).subgroupOf P.H)
    (h_quot_eq : (⟦⟨(q₀.out : G)⁻¹ * (i₀.out : G),
      P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩⟧ : decompQuot P g₂) = i')
    (hmi_coe : (i₀.out : G) = (q₀.out : G) * (i'.out : G) * (m_i : G)) :
    (uniformShiftElt P g₂ D q₀ i₀ : G) = (m_i : G)⁻¹ := by
  have hn₀_val : (i'.out : G) =
      (q₀.out : G)⁻¹ * (i₀.out : G) * (uniformShiftElt P g₂ D q₀ i₀ : G) := by
    have h1 := congr_arg (Subtype.val : ↥P.H → G) (QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct (g₂ : G) • P.H).subgroupOf P.H)
      ⟨(q₀.out : G)⁻¹ * i₀.out,
        P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩).choose_spec
    simp only [Subgroup.coe_mul] at h1
    rwa [show ((⟦⟨(q₀.out : G)⁻¹ * (i₀.out : G),
      P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩⟧ : decompQuot P g₂).out : G) =
      (i'.out : G) by congr 1; simp [h_quot_eq]] at h1
  apply representative_cancel_eq_inv (a := (i'.out : G)) (m := (m_i : G))
  conv_lhs => rw [hn₀_val, hmi_coe]
  group

private lemma heckeMultiplicity_uniform_fwdMap_injective (g₂ g₁ : P.Δ) (D : HeckeCoset P)
    (q₀ : decompQuot P (HeckeCoset.rep D)) :
    Function.Injective (heckeMultiplicity_uniform_fwdMap P g₂ g₁ D q₀) := by
  intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩ heq
  simp only [heckeMultiplicity_uniform_fwdMap, Subtype.mk.injEq, Prod.mk.injEq] at heq
  obtain ⟨hi, hj⟩ := heq
  have hi₁₂ : i₁ = i₂ := by
    rw [Quotient.eq'', QuotientGroup.leftRel_apply] at hi
    refine decompQuot_eq_of_conjAct_rel P g₂ i₁ i₂ ?_
    convert hi using 1
    ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
    group
  subst hi₁₂
  have hj₁₂ : j₁ = j₂ := by
    rw [Quotient.eq'', QuotientGroup.leftRel_apply] at hj
    refine decompQuot_eq_of_conjAct_rel P g₁ j₁ j₂ ?_
    convert hj using 1
    ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
    group
  subst hj₁₂
  rfl

private lemma heckeMultiplicity_uniform_fwdMap_surjective (g₂ g₁ : P.Δ) (D : HeckeCoset P)
    (q₀ : decompQuot P (HeckeCoset.rep D)) :
    Function.Surjective (heckeMultiplicity_uniform_fwdMap P g₂ g₁ D q₀) := by
  intro ⟨⟨i', j'⟩, (hcond'_tgt : _ = _)⟩
  let i₀ : decompQuot P g₂ :=
    ⟦⟨(q₀.out : G) * i'.out, P.H.mul_mem q₀.out.2 i'.out.2⟩⟧
  let n₀ := uniformShiftElt P g₂ D q₀ i₀
  have hn₀_conj : (g₂ : G)⁻¹ * (n₀ : G) * (g₂ : G) ∈ P.H :=
    conjAct_mem_of_subgroupOf P (g₂ : G) n₀
  let j₀ : decompQuot P g₁ := ⟦⟨(g₂ : G)⁻¹ * (n₀ : G) * (g₂ : G) * j'.out,
    P.H.mul_mem hn₀_conj j'.out.2⟩⟧
  obtain ⟨m_i, hmi_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g₂ : G) • P.H).subgroupOf P.H)
    ⟨(q₀.out : G) * i'.out, P.H.mul_mem q₀.out.2 i'.out.2⟩
  obtain ⟨m_j, hmj_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g₁ : G) • P.H).subgroupOf P.H)
    ⟨(g₂ : G)⁻¹ * (n₀ : G) * (g₂ : G) * j'.out, P.H.mul_mem hn₀_conj j'.out.2⟩
  have hmi_coe : (i₀.out : G) = (q₀.out : G) * (i'.out : G) * (m_i : G) :=
    mk_out_coe_eq_mul P hmi_eq
  have hmj_coe : (j₀.out : G) = (g₂ : G)⁻¹ * (n₀ : G) * (g₂ : G) * (j'.out : G) * (m_j : G) :=
    mk_out_coe_eq_mul P hmj_eq
  have h_quot_eq : (⟦⟨(q₀.out : G)⁻¹ * (i₀.out : G),
      P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩⟧ : decompQuot P g₂) = i' := by
    rw [(Quotient.out_eq' i').symm, Quotient.eq'', QuotientGroup.leftRel_apply]
    have h := Quotient.out_eq' i₀
    rw [Quotient.eq'', QuotientGroup.leftRel_apply] at h
    convert h using 1
    ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev]
    group
  have hcond₀ : ({(i₀.out : G) * (g₂ : G)} : Set G) * {(j₀.out : G) * (g₁ : G)} * P.H =
      {(q₀.out : G) * (HeckeCoset.rep D : G)} * P.H := by
    rw [Set.singleton_mul_singleton]
    exact coset_shift_inv P (q₀.out : G) (i₀.out : G) (j₀.out : G) (i'.out : G)
      (j'.out : G) (g₁ : G) (g₂ : G) (HeckeCoset.rep D : G) (m_i : G) (m_j : G)
      (by rw [← Set.singleton_mul_singleton]; exact hcond'_tgt)
      hmi_coe (by rw [hmj_coe,
        uniformShiftElt_eq_m_inv P g₂ D q₀ i' i₀ m_i h_quot_eq hmi_coe])
      (conjAct_mem_of_subgroupOf P (g₁ : G) m_j)
  refine ⟨⟨⟨i₀, j₀⟩, hcond₀⟩, ?_⟩
  apply Subtype.ext
  simp only [heckeMultiplicity_uniform_fwdMap, Prod.mk.injEq]
  refine ⟨h_quot_eq, ?_⟩
  rw [(Quotient.out_eq' j').symm, Quotient.eq'', QuotientGroup.leftRel_apply]
  have h_j₀ := Quotient.out_eq' j₀
  rw [Quotient.eq'', QuotientGroup.leftRel_apply] at h_j₀
  convert h_j₀ using 1
  ext
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
  group
  rfl

/-- Uniform distribution of multiplicities: the count of coset pairs `(i,j)` mapping
to a given left coset `q₀H` within double coset `D` is independent of the choice of `q₀`
(Shimura Proposition 3.4). -/
lemma heckeMultiplicity_uniform (g₂ g₁ : P.Δ) (D : HeckeCoset P)
    (q₀ : decompQuot P (HeckeCoset.rep D)) :
    Nat.card {p : decompQuot P g₂ × decompQuot P g₁ |
      ({(p.1.out : G) * (g₂ : G)} : Set G) * {(p.2.out : G) * (g₁ : G)} * P.H =
      {(q₀.out : G) * (HeckeCoset.rep D : G)} * (P.H : Set G)} =
    Nat.card {p : decompQuot P g₂ × decompQuot P g₁ |
      ({(p.1.out : G) * (g₂ : G)} : Set G) * {(p.2.out : G) * (g₁ : G)} * P.H =
      {(HeckeCoset.rep D : G)} * (P.H : Set G)} :=
  Nat.card_congr <| Equiv.ofBijective _
    ⟨heckeMultiplicity_uniform_fwdMap_injective P g₂ g₁ D q₀,
      heckeMultiplicity_uniform_fwdMap_surjective P g₂ g₁ D q₀⟩

private lemma iter_mem_smulOrbit_mulMap (g₂ g₁ β : P.Δ) (i : decompQuot P g₂)
    (j : decompQuot P g₁) :
    (⟦⟨(β : G) * i.out * (g₂ : G) * j.out * (g₁ : G),
      Submonoid.mul_mem _ (Submonoid.mul_mem _ (delta_mul_mem P.H P.Δ i.out β g₂ P.h₀)
        (P.h₀ j.out.2)) g₁.2⟩⟧ : HeckeLeftCoset P) ∈
    smulOrbit P (HeckeCoset.rep (mulMap P g₂ g₁ (i, j))) β := by
  set D := mulMap P g₂ g₁ (i, j) with hD_def
  set g_D := (HeckeCoset.rep D : G)
  set α := (β : G)
  have h_in_doset : (i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G)) ∈
      DoubleCoset.doubleCoset g_D P.H P.H := by
    rw [← HeckeCoset.toSet_eq_rep D, hD_def]
    simp only [mulMap, HeckeCoset.toSet_mk]
    exact DoubleCoset.mem_doubleCoset_self P.H P.H _
  rw [DoubleCoset.mem_doubleCoset] at h_in_doset
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := h_in_doset
  set r : decompQuot P (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct g_D • P.H).subgroupOf P.H) ⟨h₁, hh₁⟩
  suffices hsuff : (⟦⟨α * (r.out : G) * g_D,
      delta_mul_mem P.H P.Δ r.out β (HeckeCoset.rep D) P.h₀⟩⟧ :
        HeckeLeftCoset P) =
    (⟦⟨α * (i.out : G) * (g₂ : G) * (j.out : G) * (g₁ : G),
      Submonoid.mul_mem _ (Submonoid.mul_mem _
        (delta_mul_mem P.H P.Δ i.out β g₂ P.h₀)
        (P.h₀ j.out.2)) g₁.2⟩⟧ : HeckeLeftCoset P) by
    rw [← hsuff]
    simp only [smulOrbit, Finset.mem_image]
    exact ⟨r, Finset.mem_univ _, rfl⟩
  apply Quotient.sound
  change lcRel P _ _
  simp only [lcRel]
  apply leftCoset_eq_of_not_disjoint
  rw [not_disjoint_iff]
  refine ⟨α * h₁ * g_D, ?_, ?_⟩
  · refine ⟨g_D⁻¹ * (n : G)⁻¹ * g_D, conjAct_inv_mem_of_subgroupOf P g_D n, ?_⟩
    simp only [smul_eq_mul]
    rw [mk_out_coe_eq_mul P hn_eq]
    group
  · refine ⟨h₂⁻¹, P.H.inv_mem hh₂, ?_⟩
    simp only [smul_eq_mul]
    calc α * (i.out : G) * (g₂ : G) * (j.out : G) * (g₁ : G) * h₂⁻¹
        = α * ((i.out : G) * (g₂ : G) * ((j.out : G) * (g₁ : G))) * h₂⁻¹ := by group
      _ = α * (h₁ * g_D * h₂) * h₂⁻¹ := by rw [hprod]
      _ = α * h₁ * g_D := by group

private lemma rep_mem_H_of_smulOrbit_eq (g₂ β₀ : P.Δ) (i₀ : decompQuot P g₂)
    (j : HeckeLeftCoset P)
    (hj_eq : (⟦⟨(β₀ : G) * i₀.out * (g₂ : G),
      delta_mul_mem P.H P.Δ i₀.out β₀ g₂ P.h₀⟩⟧ : HeckeLeftCoset P) = j) :
    (g₂ : G)⁻¹ * (i₀.out : G)⁻¹ * (β₀ : G)⁻¹ * (HeckeLeftCoset.rep j : G) ∈ P.H := by
  set β := (HeckeLeftCoset.rep j : G)
  have h_j_set : HeckeLeftCoset.toSet j =
      ({(β₀ : G) * (i₀.out : G) * (g₂ : G)} : Set G) * ↑P.H := by
    rw [← hj_eq]
    rfl
  have hβ : β ∈ ({(β₀ : G) * (i₀.out : G) * (g₂ : G)} : Set G) * ↑P.H := by
    have h_coset : ({β} : Set G) * ↑P.H =
        ({(β₀ : G) * (i₀.out : G) * (g₂ : G)} : Set G) * ↑P.H := by
      have h1 : HeckeLeftCoset.toSet j = ({β} : Set G) * ↑P.H := by
        rw [← Quotient.out_eq (s := lcSetoid P) j]
        rfl
      rw [← h1, h_j_set]
    exact h_coset ▸ (⟨_, rfl, 1, P.H.one_mem, mul_one _⟩ : β ∈ ({β} : Set G) * ↑P.H)
  simp only [Set.singleton_mul, Set.mem_image] at hβ
  obtain ⟨h, hh, hβ_eq⟩ := hβ
  have hβ' : (g₂ : G)⁻¹ * (i₀.out : G)⁻¹ * (β₀ : G)⁻¹ * β = h := by
    rw [hβ_eq.symm]
    group
  exact hβ' ▸ hh

private lemma iter_smulOrbit_mem_mulSupport_smulOrbit (g₂ g₁ β₀ : P.Δ)
    (j x₀ : HeckeLeftCoset P) (hj : j ∈ smulOrbit P g₂ β₀)
    (hx₀ : x₀ ∈ smulOrbit P g₁ (HeckeLeftCoset.rep j)) :
    ∃ D, D ∈ mulSupport P g₂ g₁ ∧ x₀ ∈ smulOrbit P (HeckeCoset.rep D) β₀ := by
  set g₂' := (g₂ : G)
  set g₁' := (g₁ : G)
  set α := (β₀ : G)
  simp only [smulOrbit, Finset.mem_image] at hj hx₀
  obtain ⟨i₀, _, hj_eq⟩ := hj
  obtain ⟨k₀, _, hx₀_eq⟩ := hx₀
  set β := (HeckeLeftCoset.rep j : G)
  have h_rep_mem : g₂'⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β ∈ P.H :=
    rep_mem_H_of_smulOrbit_eq P g₂ β₀ i₀ j hj_eq
  set k' : decompQuot P g₁ :=
    ⟦⟨g₂'⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β * (k₀.out : G),
    P.H.mul_mem h_rep_mem k₀.out.2⟩⟧
  set D' := mulMap P g₂ g₁ (i₀, k')
  refine ⟨D', Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  rw [← hx₀_eq]
  obtain ⟨n', hn'_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct g₁' • P.H).subgroupOf P.H)
    ⟨g₂'⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β * (k₀.out : G),
      P.H.mul_mem h_rep_mem k₀.out.2⟩
  suffices hsuff :
    (⟦⟨β * (k₀.out : G) * g₁',
      delta_mul_mem P.H P.Δ k₀.out (HeckeLeftCoset.rep j) g₁ P.h₀⟩⟧ :
        HeckeLeftCoset P) =
    (⟦⟨α * (i₀.out : G) * g₂' *
      (k'.out : G) * g₁',
      Submonoid.mul_mem _ (Submonoid.mul_mem _
        (delta_mul_mem P.H P.Δ i₀.out β₀ g₂ P.h₀)
        (P.h₀ k'.out.2)) g₁.2⟩⟧ : HeckeLeftCoset P) by
    rw [hsuff]
    exact iter_mem_smulOrbit_mulMap P g₂ g₁ β₀ i₀ k'
  apply Quotient.sound
  change lcRel P _ _
  simp only [lcRel]
  apply leftCoset_eq_of_not_disjoint
  rw [not_disjoint_iff]
  refine ⟨β * (k₀.out : G) * g₁',
    ⟨1, P.H.one_mem, by simp⟩, ?_⟩
  refine ⟨g₁'⁻¹ * (n' : G)⁻¹ * g₁', conjAct_inv_mem_of_subgroupOf P g₁' n', ?_⟩
  simp only [smul_eq_mul]
  rw [mk_out_coe_eq_mul P hn'_eq]
  group

private lemma smulOrbit_indicator_eq_sum (g₁ : P.Δ) (x₀ : HeckeLeftCoset P) (β : P.Δ) :
    (if x₀ ∈ smulOrbit P g₁ β then (1 : ℤ) else 0) =
    ∑ k : decompQuot P g₁,
      if (⟦⟨(β : G) * (k.out : G) * (g₁ : G), delta_mul_mem P.H P.Δ k.out β g₁ P.h₀⟩⟧ :
        HeckeLeftCoset P) = x₀ then 1 else 0 := by
  by_cases hmem : x₀ ∈ smulOrbit P g₁ β
  · rw [if_pos hmem]
    simp only [smulOrbit, Finset.mem_image] at hmem
    obtain ⟨q₀, _, hq₀⟩ := hmem
    rw [Finset.sum_eq_single q₀]
    · rw [if_pos hq₀]
    · intro q _ hne
      rw [if_neg]
      exact fun heq ↦ hne (smulOrbit_map_injective P g₁ β (heq.trans hq₀.symm))
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  · rw [if_neg hmem]
    exact (Finset.sum_eq_zero fun q _ ↦ if_neg fun heq ↦
      hmem (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, heq⟩)).symm

private lemma singleton_coset_factor_iff (a x g₂ y g₁ z₁ z₂ : G) :
    ({a * x * g₂ * y * g₁} : Set G) * ↑P.H = {a * z₁ * z₂} * ↑P.H ↔
    ({x * g₂} : Set G) * {y * g₁} * ↑P.H = {z₁ * z₂} * ↑P.H := by
  have hl : ({a * x * g₂ * y * g₁} : Set G) =
      ({a} : Set G) * {x * g₂ * (y * g₁)} := by
    rw [Set.singleton_mul_singleton]
    congr 1
    group
  have hr : ({a * z₁ * z₂} : Set G) = ({a} : Set G) * {z₁ * z₂} := by
    rw [Set.singleton_mul_singleton]
    congr 1
    group
  constructor
  · intro h
    have hset' : ({a} : Set G) * ({x * g₂ * (y * g₁)} * ↑P.H) =
        {a} * ({z₁ * z₂} * ↑P.H) := by
      rwa [← mul_assoc, ← hl, ← mul_assoc, ← hr]
    rw [Set.singleton_mul_singleton]
    exact set_singleton_mul_left_cancel a hset'
  · intro h
    rw [Set.singleton_mul_singleton] at h
    calc ({a * x * g₂ * y * g₁} : Set G) * ↑P.H
        _ = ({a} * {x * g₂ * (y * g₁)}) * ↑P.H := by rw [hl]
        _ = {a} * ({x * g₂ * (y * g₁)} * ↑P.H) := mul_assoc _ _ _
        _ = {a} * ({z₁ * z₂} * ↑P.H) := congr_arg _ h
        _ = ({a} * {z₁ * z₂}) * ↑P.H := (mul_assoc _ _ _).symm
        _ = ({a * z₁ * z₂} : Set G) * ↑P.H := by rw [hr]

private lemma smulOrbit_count_eq_m' (g₂ g₁ : P.Δ) (D₀ : HeckeCoset P) (β₀ : P.Δ)
    (x₀ : HeckeLeftCoset P) (hx₀ : x₀ ∈ smulOrbit P (HeckeCoset.rep D₀) β₀) :
    (∑ j ∈ smulOrbit P g₂ β₀,
      if x₀ ∈ smulOrbit P g₁ (HeckeLeftCoset.rep j) then (1 : ℤ) else 0) =
    (m P g₂ g₁) D₀ := by
  simp only [smulOrbit, Finset.mem_image] at hx₀
  obtain ⟨q₀, _, hq₀⟩ := hx₀
  have h_lhs_eq : ∀ q : decompQuot P g₂,
      smulOrbit P g₁ (HeckeLeftCoset.rep
        (⟦⟨(β₀ : G) * (q.out : G) * (g₂ : G),
          delta_mul_mem P.H P.Δ q.out β₀ g₂ P.h₀⟩⟧ : HeckeLeftCoset P)) =
      smulOrbit P g₁ ⟨(β₀ : G) * (q.out : G) * (g₂ : G),
          delta_mul_mem P.H P.Δ q.out β₀ g₂ P.h₀⟩ := fun q ↦
    smulOrbit_lcRel P g₁
      (Quotient.exact (Quotient.out_eq
        (⟦⟨(β₀ : G) * (q.out : G) * (g₂ : G),
          delta_mul_mem P.H P.Δ q.out β₀ g₂ P.h₀⟩⟧ : HeckeLeftCoset P)))
  set F : HeckeLeftCoset P → ℤ :=
    fun j ↦ if x₀ ∈ smulOrbit P g₁ (HeckeLeftCoset.rep j) then 1 else 0 with hF_def
  conv_lhs => rw [smulOrbit, Finset.top_eq_univ]
  rw [Finset.sum_image (f := F) fun a _ b _ hab ↦ smulOrbit_map_injective P g₂ β₀ hab]
  simp only [hF_def, h_lhs_eq]
  simp_rw [smulOrbit_indicator_eq_sum P g₁ x₀]
  simp_rw [← hq₀, fun a b : P.Δ ↦ (⟨fun h ↦ Quotient.exact h, fun h ↦ Quotient.sound h⟩ :
    (⟦a⟧ : HeckeLeftCoset P) = ⟦b⟧ ↔ ({(a : G)} : Set G) * ↑P.H = {(b : G)} * ↑P.H)]
  rw [← Fintype.sum_prod_type', Finset.sum_boole, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  simp_rw [fun p : decompQuot P g₂ × decompQuot P g₁ ↦
    propext (singleton_coset_factor_iff P (β₀ : G) p.1.out (g₂ : G) p.2.out (g₁ : G)
      (q₀.out : G) (HeckeCoset.rep D₀ : G))]
  change _ = (heckeMultiplicity P g₂ g₁ (HeckeCoset.rep D₀) : ℤ)
  unfold heckeMultiplicity
  norm_cast
  exact heckeMultiplicity_uniform P g₂ g₁ D₀ q₀

private lemma finsupp_sum_single_orbit (orbit : Finset (HeckeLeftCoset P)) (val : ℤ)
    (f : HeckeLeftCoset P → ℤ → ℤ) (hf0 : ∀ a, f a 0 = 0)
    (hfadd : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
    (∑ j ∈ orbit, Finsupp.single j val).sum f = ∑ j ∈ orbit, f j val := by
  rw [← Finsupp.sum_finset_sum_index (h_zero := hf0) (h_add := hfadd)]
  exact Finset.sum_congr rfl fun j _ ↦ Finsupp.sum_single_index (hf0 j)

private lemma smul_assoc_key (g₁ g₂ β₀ : P.Δ) :
    ((m P g₂ g₁).sum fun D b₁ ↦
      ∑ i ∈ smulOrbit P (HeckeCoset.rep D) β₀, Finsupp.single i (b₁ * 1)) =
    (∑ j ∈ smulOrbit P g₂ β₀,
      Finsupp.single j 1).sum
      fun m b₂ ↦ ∑ i ∈ smulOrbit P g₁ (HeckeLeftCoset.rep m),
        Finsupp.single i (1 * b₂) := by
  simp only [mul_one, one_mul]
  ext x₀
  simp only [Finsupp.sum_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp_rw [Finset.sum_ite_eq']
  rw [finsupp_sum_single_orbit P _ 1 _ (fun a ↦ by simp)
    (fun a b₁ b₂ ↦ by split_ifs <;> simp [*])]
  by_cases h_ex : ∃ D₀ ∈ (m P g₂ g₁).support, x₀ ∈ smulOrbit P (HeckeCoset.rep D₀) β₀
  · obtain ⟨D₀, hD₀, hx₀⟩ := h_ex
    have h_lhs : (m P g₂ g₁).sum (fun a₁ b ↦
        if x₀ ∈ smulOrbit P (HeckeCoset.rep a₁) β₀ then b
        else (0 : ℤ)) = (m P g₂ g₁) D₀ := by
      rw [Finsupp.sum, Finset.sum_eq_single D₀
        (fun D hD hne ↦ if_neg (Finset.disjoint_left.mp
          (smulOrbit_disjoint_of_ne P (HeckeCoset.rep D₀) (HeckeCoset.rep D) β₀
            (by simpa only [HeckeCoset.rep, Quotient.out_eq] using hne.symm)) hx₀))
        (fun h ↦ absurd hD₀ h)]
      exact if_pos hx₀
    rw [h_lhs]
    exact (smulOrbit_count_eq_m' P g₂ g₁ D₀ β₀ x₀ hx₀).symm
  · push Not at h_ex
    have h_lhs : (m P g₂ g₁).sum (fun a₁ b ↦
        if x₀ ∈ smulOrbit P (HeckeCoset.rep a₁) β₀ then b
        else (0 : ℤ)) = 0 := by
      rw [Finsupp.sum]
      exact Finset.sum_eq_zero fun D hD ↦ if_neg (h_ex D hD)
    rw [h_lhs]
    exact (Finset.sum_eq_zero fun j hj ↦ by
      simp only [ite_eq_right_iff, one_ne_zero]
      intro hmem
      obtain ⟨D, hD, hD_mem⟩ :=
        iter_smulOrbit_mem_mulSupport_smulOrbit
          P g₂ g₁ β₀ j x₀ hj hmem
      exact absurd hD_mem (h_ex D hD)).symm

private lemma smul_assoc_singles_lhs_apply (D₁ D₂ : HeckeCoset P) (a₁ a₂ : ℤ)
    (m₀ x₀ : HeckeLeftCoset P) (c₀ : ℤ) :
    ((a₂ • a₁ • m P D₂.rep D₁.rep).sum fun D1 b₁ ↦
      ∑ i ∈ smulOrbit P D1.rep m₀.rep, Finsupp.single i (b₁ * c₀)) x₀ =
    a₁ * a₂ * c₀ *
      (m P D₂.rep D₁.rep).sum
        (fun D b₁ ↦ if x₀ ∈ smulOrbit P D.rep m₀.rep then b₁ else (0 : ℤ)) := by
  simp only [Finsupp.sum_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp_rw [Finset.sum_ite_eq']
  have h_lhs : (a₂ • a₁ • m P D₂.rep D₁.rep).sum
      (fun D b₁ ↦ if x₀ ∈ smulOrbit P D.rep m₀.rep then b₁ * c₀ else (0 : ℤ)) =
      (m P D₂.rep D₁.rep).sum
      (fun D b₁ ↦
        if x₀ ∈ smulOrbit P D.rep m₀.rep then a₂ * (a₁ * b₁) * c₀ else (0 : ℤ)) := by
    rw [Finsupp.sum_smul_index (fun i ↦ by split_ifs <;> simp),
      Finsupp.sum_smul_index (fun i ↦ by split_ifs <;> simp)]
  rw [h_lhs, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun D _ ↦ ?_
  dsimp only
  split_ifs <;> ring

private lemma smul_assoc_singles_rhs_apply (D₁ D₂ : HeckeCoset P) (a₁ a₂ : ℤ)
    (m₀ x₀ : HeckeLeftCoset P) (c₀ : ℤ) :
    ((∑ i ∈ smulOrbit P D₂.rep m₀.rep, Finsupp.single i (a₂ * c₀)).sum fun m b₂ ↦
      ∑ i ∈ smulOrbit P D₁.rep m.rep, Finsupp.single i (a₁ * b₂)) x₀ =
    a₁ * a₂ * c₀ *
      ∑ j ∈ smulOrbit P D₂.rep m₀.rep,
        if x₀ ∈ smulOrbit P D₁.rep j.rep then (1 : ℤ) else 0 := by
  simp only [Finsupp.sum_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp_rw [Finset.sum_ite_eq']
  rw [finsupp_sum_single_orbit P _ (a₂ * c₀) _ (fun a ↦ by simp)
    (fun a b₁ b₂ ↦ by split_ifs <;> simp [*, mul_add])]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp only
  split_ifs <;> ring

private lemma smul_assoc_singles_sum_eq (D₁ D₂ : HeckeCoset P) (a₁ a₂ : ℤ)
    (m₀ : HeckeLeftCoset P) (c₀ : ℤ) :
    ((a₂ • a₁ • m P D₂.rep D₁.rep).sum fun D1 b₁ ↦
      ∑ i ∈ smulOrbit P D1.rep m₀.rep, Finsupp.single i (b₁ * c₀)) =
    (∑ i ∈ smulOrbit P D₂.rep m₀.rep, Finsupp.single i (a₂ * c₀)).sum fun m b₂ ↦
      ∑ i ∈ smulOrbit P D₁.rep m.rep, Finsupp.single i (a₁ * b₂) := by
  ext x₀
  rw [smul_assoc_singles_lhs_apply P D₁ D₂ a₁ a₂ m₀ x₀ c₀,
    smul_assoc_singles_rhs_apply P D₁ D₂ a₁ a₂ m₀ x₀ c₀]
  congr 1
  have key := smul_assoc_key P D₁.rep D₂.rep m₀.rep
  simp only [mul_one, one_mul] at key
  have key_pt := DFunLike.congr_fun key x₀
  simp only [Finsupp.sum_apply, Finsupp.finset_sum_apply, Finsupp.single_apply] at key_pt
  simp_rw [Finset.sum_ite_eq'] at key_pt
  rw [key_pt]
  exact finsupp_sum_single_orbit P _ 1 _ (fun a ↦ by simp)
    (fun a b₁ b₂ ↦ by split_ifs <;> simp [*])

private lemma smul_assoc_singles (D₁ D₂ : HeckeCoset P) (a₁ a₂ : ℤ)
    (m₀ : HeckeLeftCoset P) (c₀ : ℤ) :
    (T_single P ℤ D₂ a₂ * T_single P ℤ D₁ a₁) •
      (HeckeLeftCoset_single P ℤ m₀ c₀) =
    T_single P ℤ D₁ a₁ •
      (T_single P ℤ D₂ a₂ • HeckeLeftCoset_single P ℤ m₀ c₀) := by
  rw [mul_singleton_𝕋, single_smul_single]
  simp only [smul_eq_sum, HeckeLeftCoset_single, T_single]
  have hsi : ∀ (D : HeckeCoset P) (b : ℤ),
      (Finsupp.single m₀ c₀).sum (fun m b₂ ↦
        ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m),
          Finsupp.single i (b * b₂)) =
      ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m₀),
        Finsupp.single i (b * c₀) := by
    intro D b
    rw [Finsupp.sum_single_index (by
      simp [mul_zero, Finsupp.single_zero,
        Finset.sum_const_zero])]
  simp_rw [hsi]
  rw [Finsupp.sum_single_index (by simp [zero_mul, Finsupp.single_zero, Finset.sum_const_zero])]
  exact smul_assoc_singles_sum_eq P D₁ D₂ a₁ a₂ m₀ c₀

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
