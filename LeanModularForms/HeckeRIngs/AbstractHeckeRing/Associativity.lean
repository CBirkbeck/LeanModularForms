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

variable {G α : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G) (h₀ : H.toSubmonoid ≤ Δ)
  (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

variable (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] [IsDomain Z]

open Finsupp

/-- IsScalarTower: x •_M (y •_M z) = (y * x) •_M z. This is Shimura Prop 3.4
    adapted to right cosets with opposite SMul convention. The key identity is that
    the iterated module action (apply D₂ then D₁) produces the same Finsupp as
    the Hecke product (D₂ * D₁) applied once, because both count pairs
    (j, i) ∈ Q(D₂) × Q(D₁) with j·g₂·i·g₁ landing in the appropriate right coset. -/
private lemma smulOrbit_map_injective (D : T' P) (m₀ : M P) :
    Function.Injective (fun i : decompQuot P D =>
      M_mk P ⟨((m₀.eql.choose : G) * (i.out : G) *
        (D.eql.choose : G)),
        delta_mul_mem P.H P.Δ i.out
          m₀.eql.choose D.eql.choose P.h₀⟩) := by
  intro i₁ i₂ heq
  by_contra hne
  have hset := congr_arg M.set heq
  simp only [M_mk] at hset
  have hmem : (m₀.eql.choose : G) * (i₁.out : G) * (D.eql.choose : G) ∈
      ({(m₀.eql.choose : G) * (i₂.out : G) * (D.eql.choose : G)} : Set G) * (P.H : Set G) := by
    rw [← hset]; exact ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, ha, k, hk, hkk⟩ := hmem
  rw [Set.mem_singleton_iff] at ha; subst ha
  have cancel : (i₂.out : G) * (D.eql.choose : G) * k = (i₁.out : G) * (D.eql.choose : G) := by
    apply mul_left_cancel (a := (m₀.eql.choose : G))
    have := hkk; group at this ⊢; exact this
  apply decompQuot_coset_diff P D i₁ i₂ hne
  exact leftCoset_eq_of_not_disjoint (H := P.H) _ _ (by
    rw [@not_disjoint_iff]
    exact ⟨(i₁.out : G) * (D.eql.choose : G),
      ⟨1, P.H.one_mem, mul_one _⟩,
      ⟨k, hk, cancel⟩⟩)

/-- The smulOrbit Finset.sum can be rewritten as a sum over Q. -/
private lemma smulOrbit_sum_eq (D : T' P) (m₀ : M P) (f : M P → (M P) →₀ ℤ) :
    ∑ i ∈ smulOrbit P D m₀, f i =
    ∑ q : decompQuot P D, f (M_mk P
      ⟨((m₀.eql.choose : G) * (q.out : G) *
        (D.eql.choose : G)),
        delta_mul_mem P.H P.Δ q.out
          m₀.eql.choose D.eql.choose P.h₀⟩) := by
  rw [smulOrbit, Finset.sum_image (fun a _ b _ hab => smulOrbit_map_injective P D m₀ hab)]
  rfl

/-- Key lemma: m'(D₂, D₁, D) counts the pairs whose
    smulOrbit-iterated action lands in smulOrbit(D, m₀).
    This is the "uniform distribution" property that bridges multiplication and module action. -/
private lemma M_ext_set (m₁ m₂ : M P) (h : m₁.set = m₂.set) : m₁ = m₂ := by
  rcases m₁ with ⟨s₁, e₁⟩; rcases m₂ with ⟨s₂, e₂⟩
  obtain rfl : s₁ = s₂ := h; rfl

/-- smulOrbit(D, m) = smulOrbit(D, m') when m and m' represent the same right coset.
    This is key for representative independence. -/
private lemma smulOrbit_congr (D : T' P) (m₁ m₂ : M P) (h : m₁ = m₂) :
    smulOrbit P D m₁ = smulOrbit P D m₂ := h ▸ rfl

/-- The smulOrbit formal sum is invariant under left-multiplication of the base element by h ∈ H.
    This is because left-multiplication by h permutes Q(D), and the N-absorption property
    ensures the M_mk values match. -/
private lemma smulOrbit_sum_left_H_eq (D : T' P) (β : P.Δ) (h : P.H) (c : ℤ) :
    ∑ q : decompQuot P D, Finsupp.single
      (M_mk P ⟨(β : G) * (h : G) * q.out *
        (D.eql.choose : G),
      Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ β.2 (P.h₀ h.2))
        (P.h₀ q.out.2)) D.eql.choose.2⟩) c =
    ∑ q : decompQuot P D, Finsupp.single (M_mk P ⟨(β : G) * q.out * (D.eql.choose : G),
      delta_mul_mem P.H P.Δ q.out β D.eql.choose P.h₀⟩) c := by
  set g := (D.eql.choose : G) with hg_def
  set σ : decompQuot P D → decompQuot P D :=
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
        (⟦⟨(h : G)⁻¹ * q.out, P.H.mul_mem (P.H.inv_mem h.2) q.out.2⟩⟧ : decompQuot P D)
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hout
      convert hout using 1; ext; simp [Subgroup.coe_mul]; group
  have hval : ∀ q : decompQuot P D,
      M_mk P ⟨(β : G) * (h : G) * q.out * g,
        Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ β.2 (P.h₀ h.2))
          (P.h₀ q.out.2)) D.eql.choose.2⟩ =
      M_mk P ⟨(β : G) * (σ q).out * g,
        delta_mul_mem P.H P.Δ (σ q).out β D.eql.choose P.h₀⟩ := by
    intro q
    apply M_ext_set
    simp only [M_mk, σ]
    obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g • P.H).subgroupOf P.H) ⟨h * q.out, P.H.mul_mem h.2 q.out.2⟩
    have hn_coe : ((⟦⟨(h : G) * (q.out : G),
        P.H.mul_mem h.2 q.out.2⟩⟧ :
        decompQuot P D).out : G) =
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

/-- If `n ∈ (ConjAct g • H).subgroupOf H`, then `g⁻¹ * n⁻¹ * g ∈ H`.
    This extracts the conjugation membership that appears throughout the associativity proof. -/
private lemma conjAct_inv_mem_of_subgroupOf (g : G)
    (n : (ConjAct.toConjAct g • P.H).subgroupOf P.H) :
    g⁻¹ * (n : G)⁻¹ * g ∈ P.H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hn
  have := P.H.inv_mem hn; convert this using 1; group

/-- Variant of `conjAct_inv_mem_of_subgroupOf` without the inverse on `n`. -/
private lemma conjAct_mem_of_subgroupOf (g : G) (n : (ConjAct.toConjAct g • P.H).subgroupOf P.H) :
    g⁻¹ * (n : G) * g ∈ P.H := by
  have hn := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hn
  simpa [ConjAct.ofConjAct_toConjAct] using hn

/-- Extract the coercion from `QuotientGroup.mk_out_eq_mul`: if `⟦h⟧.out = h * n`, then
    `(⟦h⟧.out : G) = (h : G) * (n : G)`. -/
private lemma mk_out_coe_eq_mul {g : G} {h : P.H}
    {n : (ConjAct.toConjAct g • P.H).subgroupOf P.H}
    (hn_eq : (⟦h⟧ : P.H ⧸ (ConjAct.toConjAct g • P.H).subgroupOf P.H).out = h * n) :
    ((⟦h⟧ : P.H ⧸ (ConjAct.toConjAct g • P.H).subgroupOf P.H).out : G) =
      (h : G) * (n : G) := by
  have := congr_arg (Subtype.val : ↥P.H → G) hn_eq
  simpa [Subgroup.coe_mul] using this

/-- Two `decompQuot` elements `i₁, i₂` are equal when `i₁.out⁻¹ * i₂.out` lies in the
    conjugate-stabilizer subgroup `(ConjAct g • H).subgroupOf H`. This handles the
    `Quotient.eq''` + `leftRel_apply` + `Quotient.out_eq'` chain that appears 4 times. -/
private lemma decompQuot_eq_of_conjAct_rel (D : T' P) (i₁ i₂ : decompQuot P D)
    (h : (i₁.out : ↥P.H)⁻¹ * i₂.out ∈
      (ConjAct.toConjAct (D.eql.choose : G) • P.H).subgroupOf P.H) :
    i₁ = i₂ := by
  rw [← @QuotientGroup.leftRel_apply, ← @Quotient.eq''] at h
  simp only [Quotient.out_eq'] at h; exact h

/-- Shifted coset condition: if `a * g₂ * (b * g₁) ∈ (q * g_D) · H` and the group elements
    `a', b'` are related to `a, b` by `a' = q⁻¹ * a * n₁` and
    `b' = (g₂⁻¹ * n₁⁻¹ * g₂) * b * n₂` where `n₁, n₂` conjugate into H,
    then `a' * g₂ * (b' * g₁) ∈ g_D · H`. -/
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

/-- Inverse-shifted coset condition: if `a' * g₂ * (b' * g₁) ∈ g_D · H` and
    the group elements `a, b` are related to `a', b'` by `a = q * a' * m₁`
    and `b = (g₂⁻¹ * m₁⁻¹ * g₂) * b' * m₂` where `m₂` conjugates into H,
    then `a * g₂ * (b * g₁) ∈ (q * g_D) · H`. -/
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

/-- Uniform distribution: the count m'(D₂, D₁, D) is the same whether we count pairs
    landing in g_D·H or in q₀.out·g_D·H (any right coset within double coset D).
    This is the key to Shimura's Proposition 3.4 (associativity of the Hecke product). -/
lemma m'_uniform (D₂ D₁ D : T' P) (q₀ : decompQuot P D) :
    Nat.card {p : decompQuot P D₂ × decompQuot P D₁ |
      ({(p.1.out : G) * (D₂.eql.choose : G)} : Set G) *
      {(p.2.out : G) * (D₁.eql.choose : G)} * P.H =
      {(q₀.out : G) * (D.eql.choose : G)} * (P.H : Set G)} =
    Nat.card {p : decompQuot P D₂ × decompQuot P D₁ |
      ({(p.1.out : G) * (D₂.eql.choose : G)} : Set G) *
      {(p.2.out : G) * (D₁.eql.choose : G)} * P.H =
      {(D.eql.choose : G)} * (P.H : Set G)} := by
  set g₁ := (D₁.eql.choose : G) with hg₁_def
  set g₂ := (D₂.eql.choose : G) with hg₂_def
  set g_D := (D.eql.choose : G) with hgD_def
  apply Nat.card_congr
  let get_n : decompQuot P D₂ → (ConjAct.toConjAct g₂ • P.H).subgroupOf P.H := fun i =>
    (QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g₂ • P.H).subgroupOf P.H)
      ⟨(q₀.out : G)⁻¹ * i.out, P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩).choose
  refine Equiv.ofBijective (fun ⟨⟨i, j⟩, (hcond : _ = _)⟩ =>
    let i' : decompQuot P D₂ :=
      ⟦⟨(q₀.out : G)⁻¹ * i.out,
        P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩⟧
    let n := get_n i
    let hn_conj : g₂⁻¹ * (n : G)⁻¹ * g₂ ∈ P.H := conjAct_inv_mem_of_subgroupOf P g₂ n
    let h_n : G := g₂⁻¹ * (n : G)⁻¹ * g₂
    let j' : decompQuot P D₁ := ⟦⟨h_n * j.out, P.H.mul_mem hn_conj j.out.2⟩⟧
    (⟨⟨i', j'⟩, by
      show ({(i'.out : G) * g₂} : Set G) * {(j'.out : G) * g₁} * P.H = {g_D} * P.H
      rw [Set.singleton_mul_singleton]
      have hcond' : ({(i.out : G) * g₂ * ((j.out : G) * g₁)} : Set G) * ↑P.H =
          {(q₀.out : G) * g_D} * ↑P.H := by
        rw [← Set.singleton_mul_singleton]; exact hcond
      have hn_coe : (i'.out : G) = (q₀.out : G)⁻¹ * (i.out : G) * (n : G) :=
        mk_out_coe_eq_mul P (QuotientGroup.mk_out_eq_mul
          ((ConjAct.toConjAct g₂ • P.H).subgroupOf P.H)
          ⟨(q₀.out : G)⁻¹ * i.out,
            P.H.mul_mem (P.H.inv_mem q₀.out.2) i.out.2⟩).choose_spec
      obtain ⟨n', hn'_eq⟩ := QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct g₁ • P.H).subgroupOf P.H)
        ⟨h_n * j.out, P.H.mul_mem hn_conj j.out.2⟩
      exact coset_shift_fwd P (q₀.out : G) (i.out : G) (j.out : G) (i'.out : G)
        (j'.out : G) g₁ g₂ g_D (n : G) (n' : G) hcond' hn_coe
        (mk_out_coe_eq_mul P hn'_eq) (conjAct_mem_of_subgroupOf P g₁ n')
    ⟩ : {p : decompQuot P D₂ × decompQuot P D₁ |
      ({(p.1.out : G) * g₂} : Set G) * {(p.2.out : G) * g₁} * P.H =
      {g_D} * P.H})) ?_
  constructor
  · intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩ heq
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
    obtain ⟨hi, hj⟩ := heq
    have hi₁₂ : i₁ = i₂ := by
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hi
      exact decompQuot_eq_of_conjAct_rel P D₂ i₁ i₂
        (by convert hi using 1; ext; simp [Subgroup.coe_mul]; group)
    subst hi₁₂
    have hj₁₂ : j₁ = j₂ := by
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hj
      exact decompQuot_eq_of_conjAct_rel P D₁ j₁ j₂
        (by convert hj using 1; ext; simp [Subgroup.coe_mul]; group)
    subst hj₁₂; rfl
  · intro ⟨⟨i', j'⟩, (hcond'_tgt : _ = _)⟩
    let i₀ : decompQuot P D₂ :=
      ⟦⟨(q₀.out : G) * i'.out, P.H.mul_mem q₀.out.2 i'.out.2⟩⟧
    let n₀ := get_n i₀
    have hn₀_conj : g₂⁻¹ * (n₀ : G) * g₂ ∈ P.H := conjAct_mem_of_subgroupOf P g₂ n₀
    let j₀ : decompQuot P D₁ := ⟦⟨g₂⁻¹ * (n₀ : G) * g₂ * j'.out,
      P.H.mul_mem hn₀_conj j'.out.2⟩⟧
    obtain ⟨m_i, hmi_eq⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g₂ • P.H).subgroupOf P.H)
      ⟨(q₀.out : G) * i'.out, P.H.mul_mem q₀.out.2 i'.out.2⟩
    obtain ⟨m_j, hmj_eq⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct g₁ • P.H).subgroupOf P.H)
      ⟨g₂⁻¹ * (n₀ : G) * g₂ * j'.out, P.H.mul_mem hn₀_conj j'.out.2⟩
    have hmi_coe : (i₀.out : G) = (q₀.out : G) * (i'.out : G) * (m_i : G) :=
      mk_out_coe_eq_mul P hmi_eq
    have hmj_coe : (j₀.out : G) = g₂⁻¹ * (n₀ : G) * g₂ * (j'.out : G) * (m_j : G) :=
      mk_out_coe_eq_mul P hmj_eq
    have h_quot_eq : (⟦⟨(q₀.out : G)⁻¹ * (i₀.out : G),
        P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩⟧ : decompQuot P D₂) = i' := by
      rw [show i' = ⟦i'.out⟧ from (Quotient.out_eq' i').symm, @Quotient.eq'',
        QuotientGroup.leftRel_apply]
      have h := Quotient.out_eq' i₀
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at h
      convert h using 1; ext; simp [Subgroup.coe_mul]; group
    have h_n₀_mi : (n₀ : G) = (m_i : G)⁻¹ := by
      have hn₀_spec := (QuotientGroup.mk_out_eq_mul
        ((ConjAct.toConjAct g₂ • P.H).subgroupOf P.H)
        ⟨(q₀.out : G)⁻¹ * i₀.out,
          P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩).choose_spec
      have hn₀_val : (i'.out : G) = (q₀.out : G)⁻¹ * (i₀.out : G) * (n₀ : G) := by
        have h1 := congr_arg (Subtype.val : ↥P.H → G) hn₀_spec
        simp only [Subgroup.coe_mul] at h1
        rwa [show ((⟦⟨(q₀.out : G)⁻¹ * (i₀.out : G),
          P.H.mul_mem (P.H.inv_mem q₀.out.2) i₀.out.2⟩⟧ : decompQuot P D₂).out : G) =
          (i'.out : G) from by congr 1; simp [h_quot_eq]] at h1
      have h1 : (i'.out : G) = (i'.out : G) * (m_i : G) * (n₀ : G) := by
        conv_lhs => rw [hn₀_val]; rw [hmi_coe]
        group
      have h2 : (m_i : G) * (n₀ : G) = 1 := by
        have := congr_arg ((i'.out : G)⁻¹ * ·) h1
        simp only [inv_mul_cancel] at this; group at this; exact this.symm
      exact eq_inv_of_mul_eq_one_right h2
    have hcond₀ : ({(i₀.out : G) * g₂} : Set G) * {(j₀.out : G) * g₁} * P.H =
        {(q₀.out : G) * g_D} * P.H := by
      rw [Set.singleton_mul_singleton]
      exact coset_shift_inv P (q₀.out : G) (i₀.out : G) (j₀.out : G) (i'.out : G)
        (j'.out : G) g₁ g₂ g_D (m_i : G) (m_j : G)
        (by rw [← Set.singleton_mul_singleton]; exact hcond'_tgt)
        hmi_coe (by rw [hmj_coe, h_n₀_mi]) (conjAct_mem_of_subgroupOf P g₁ m_j)
    refine ⟨⟨⟨i₀, j₀⟩, hcond₀⟩, ?_⟩
    apply Subtype.ext; simp only [Prod.mk.injEq]; exact ⟨h_quot_eq, by
      rw [show j' = ⟦j'.out⟧ from (Quotient.out_eq' j').symm, @Quotient.eq'',
        QuotientGroup.leftRel_apply]
      have h_j₀ := Quotient.out_eq' j₀
      rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at h_j₀
      convert h_j₀ using 1; ext; simp [Subgroup.coe_mul]; group; rfl⟩

/-- The iterated product M_mk(α * i * g₂ * j * g₁) lies in
    smulOrbit(mulMap(D₂,D₁,(i,j)), m₀).
    This is the composition lemma: if we apply smulOrbit for D₂ then smulOrbit for D₁,
    the result lands in smulOrbit for the composed double coset. -/
private lemma iter_mem_smulOrbit_mulMap (D₂ D₁ : T' P) (m₀ : M P)
    (i : decompQuot P D₂) (j : decompQuot P D₁) :
    M_mk P ⟨(m₀.eql.choose : G) * i.out * (D₂.eql.choose : G) *
      j.out * (D₁.eql.choose : G),
      Submonoid.mul_mem _ (Submonoid.mul_mem _
        (delta_mul_mem P.H P.Δ i.out m₀.eql.choose D₂.eql.choose P.h₀)
        (P.h₀ j.out.2)) D₁.eql.choose.2⟩ ∈
    smulOrbit P (mulMap P D₂ D₁ (i, j)) m₀ := by
  set D := mulMap P D₂ D₁ (i, j) with hD_def
  set g_D := (D.eql.choose : G) with hgD_def
  set α := (m₀.eql.choose : G)
  set g₁ := (D₁.eql.choose : G)
  set g₂ := (D₂.eql.choose : G)
  have h_in_doset : (i.out : G) * g₂ * ((j.out : G) * g₁) ∈
      DoubleCoset.doubleCoset g_D P.H P.H := by
    have h1 : D.set = DoubleCoset.doubleCoset g_D P.H P.H := D.eql.choose_spec
    rw [← h1]
    show (i.out : G) * g₂ * ((j.out : G) * g₁) ∈ (mulMap P D₂ D₁ (i, j)).set
    simp only [mulMap, T_mk]
    exact DoubleCoset.mem_doubleCoset_self P.H P.H _
  rw [DoubleCoset.mem_doubleCoset] at h_in_doset
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := h_in_doset
  set r : decompQuot P D := ⟦⟨h₁, hh₁⟩⟧
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
  suffices hsuff : M_mk P ⟨α * (r.out : G) * g_D,
      delta_mul_mem P.H P.Δ r.out m₀.eql.choose D.eql.choose P.h₀⟩ =
    M_mk P ⟨α * (i.out : G) * g₂ * (j.out : G) * g₁,
      Submonoid.mul_mem _ (Submonoid.mul_mem _
        (delta_mul_mem P.H P.Δ i.out m₀.eql.choose D₂.eql.choose P.h₀)
        (P.h₀ j.out.2)) D₁.eql.choose.2⟩ by
    rw [← hsuff]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ r)
  apply M_ext_set; simp only [M_mk]
  apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
  refine ⟨α * h₁ * g_D, ?_, ?_⟩
  · refine ⟨g_D⁻¹ * (n : G)⁻¹ * g_D, hn_conj, ?_⟩
    simp only [smul_eq_mul]; rw [hn_coe]; group
  · refine ⟨h₂⁻¹, P.H.inv_mem hh₂, ?_⟩
    simp only [smul_eq_mul]
    have hprod' : (i.out : G) * g₂ * ((j.out : G) * g₁) = h₁ * g_D * h₂ := hprod
    calc α * (i.out : G) * g₂ * (j.out : G) * g₁ * h₂⁻¹
        = α * ((i.out : G) * g₂ * ((j.out : G) * g₁)) * h₂⁻¹ := by group
      _ = α * (h₁ * g_D * h₂) * h₂⁻¹ := by rw [hprod']
      _ = α * h₁ * g_D := by group

/-- If j ∈ smulOrbit(D₂, m₀) and x₀ ∈ smulOrbit(D₁, j),
    then x₀ ∈ smulOrbit(D, m₀) for some
    D ∈ mulSupport(D₂, D₁).
    This is the "composition" lemma for iterated module actions. -/
private lemma iter_smulOrbit_mem_mulSupport_smulOrbit (D₂ D₁ : T' P) (m₀ j x₀ : M P)
    (hj : j ∈ smulOrbit P D₂ m₀) (hx₀ : x₀ ∈ smulOrbit P D₁ j) :
    ∃ D, D ∈ mulSupport P D₂ D₁ ∧ x₀ ∈ smulOrbit P D m₀ := by
  simp only [smulOrbit, Finset.mem_image] at hj hx₀
  obtain ⟨i₀, _, hj_eq⟩ := hj
  obtain ⟨k₀, _, hx₀_eq⟩ := hx₀
  set α := (m₀.eql.choose : G)
  set g₁ := (D₁.eql.choose : G)
  set g₂ := (D₂.eql.choose : G)
  have h_j_set : j.set = ({α * (i₀.out : G) * g₂} : Set G) * ↑P.H := by
    rw [← hj_eq]; rfl
  set β := (j.eql.choose : G) with hβ_def
  have h_rep_mem : g₂⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β ∈ P.H := by
    have h_coset : ({β} : Set G) * ↑P.H = ({α * (i₀.out : G) * g₂} : Set G) * ↑P.H := by
      rw [← j.eql.choose_spec, h_j_set]
    have hβ : β ∈ ({α * (i₀.out : G) * g₂} : Set G) * ↑P.H := by
      have h1 := Set.mul_mem_mul
        (show β ∈ ({β} : Set G) from rfl)
        (show (1 : G) ∈ (↑P.H : Set G) from P.H.one_mem)
      rwa [mul_one, h_coset] at h1
    simp only [Set.singleton_mul, Set.mem_image] at hβ
    obtain ⟨h, hh, hβ_eq⟩ := hβ
    have : g₂⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β = h := by
      rw [show β = α * (i₀.out : G) * g₂ * h from hβ_eq.symm]; group
    rw [this]; exact hh
  set k' : decompQuot P D₁ :=
    ⟦⟨g₂⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β *
      (k₀.out : G),
    P.H.mul_mem h_rep_mem k₀.out.2⟩⟧
  set D := mulMap P D₂ D₁ (i₀, k')
  refine ⟨D, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have h_target := iter_mem_smulOrbit_mulMap P D₂ D₁ m₀ i₀ k'
  rw [← hx₀_eq]
  obtain ⟨n', hn'_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct g₁ • P.H).subgroupOf P.H)
    ⟨g₂⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β *
      (k₀.out : G),
      P.H.mul_mem h_rep_mem k₀.out.2⟩
  have hn'_coe : (k'.out : G) =
      g₂⁻¹ * (i₀.out : G)⁻¹ * α⁻¹ * β *
        (k₀.out : G) * (n' : G) := by
    have := congr_arg (Subtype.val : ↥P.H → G) hn'_eq
    simpa [Subgroup.coe_mul] using this
  have hn'_conj : g₁⁻¹ * (n' : G) * g₁ ∈ P.H := by
    have := n'.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at this
    exact this
  suffices hsuff : M_mk P ⟨β * (k₀.out : G) * g₁,
      delta_mul_mem P.H P.Δ k₀.out j.eql.choose D₁.eql.choose P.h₀⟩ =
    M_mk P ⟨α * (i₀.out : G) * g₂ * (k'.out : G) * g₁,
      Submonoid.mul_mem _ (Submonoid.mul_mem _
        (delta_mul_mem P.H P.Δ i₀.out m₀.eql.choose D₂.eql.choose P.h₀)
        (P.h₀ k'.out.2)) D₁.eql.choose.2⟩ by
    rw [hsuff]; exact h_target
  apply M_ext_set; simp only [M_mk]
  apply leftCoset_eq_of_not_disjoint; rw [@not_disjoint_iff]
  refine ⟨β * (k₀.out : G) * g₁, ?_, ?_⟩
  · exact ⟨1, P.H.one_mem, by simp [smul_eq_mul]⟩
  · have hn'_inv_conj : g₁⁻¹ * (n' : G)⁻¹ * g₁ ∈ P.H := by
      have := P.H.inv_mem hn'_conj; convert this using 1; group
    refine ⟨g₁⁻¹ * (n' : G)⁻¹ * g₁, hn'_inv_conj, ?_⟩
    simp only [smul_eq_mul]; rw [hn'_coe]; group

/-- For each i : Q D₂, the membership indicator
    x₀ ∈ smulOrbit D₁ j_i (where j_i = M_mk(α*i*g₂))
    equals the sum of indicators over Q D₁. This uses smulOrbit_sum_left_H_eq to handle the
    representative mismatch between j_i.eql.choose and α*i*g₂. -/
private lemma smulOrbit_indicator_eq_sum (D₁ : T' P) (_m₀ : M P) (x₀ : M P) (β : P.Δ) :
    (if x₀ ∈ smulOrbit P D₁ (M_mk P β) then (1 : ℤ) else 0) =
    ∑ k : decompQuot P D₁, if M_mk P ⟨(β : G) * (k.out : G) * (D₁.eql.choose : G),
      delta_mul_mem P.H P.Δ k.out β D₁.eql.choose P.h₀⟩ = x₀ then 1 else 0 := by
  set g₁ := (D₁.eql.choose : G)
  set j := M_mk P β
  set γ := (j.eql.choose : G) with hγ_def
  have h_rep_mem : (β : G)⁻¹ * γ ∈ P.H := by
    have h_set : j.set = ({(β : G)} : Set G) * ↑P.H := rfl
    have h_choose : j.set = ({γ} : Set G) * ↑P.H := j.eql.choose_spec
    rw [h_set] at h_choose
    have hγ_mem_rhs : γ ∈ ({γ} : Set G) * ↑P.H :=
      ⟨γ, Set.mem_singleton _, 1, P.H.one_mem, mul_one γ⟩
    have hγ : γ ∈ ({(β : G)} : Set G) * ↑P.H := h_choose ▸ hγ_mem_rhs
    simp only [Set.singleton_mul, Set.mem_image] at hγ
    obtain ⟨h, hh, hγ_eq⟩ := hγ
    have : (β : G)⁻¹ * γ = h := by rw [show γ = (β : G) * h from hγ_eq.symm]; group
    rw [this]; exact hh
  set h_rep : P.H := ⟨(β : G)⁻¹ * γ, h_rep_mem⟩
  have h_sum := smulOrbit_sum_left_H_eq P D₁ β h_rep 1
  have h_pt := congr_fun (congr_arg DFunLike.coe h_sum) x₀
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply] at h_pt
  have h_eq_γ : (β : G) * (h_rep : G) = γ := by
    show (β : G) * ((β : G)⁻¹ * γ) = γ; group
  have h_lhs_eq : (∑ x : decompQuot P D₁,
      if M_mk P ⟨(β : G) * (h_rep : G) *
        ↑(Quotient.out x) * g₁,
      Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ β.2 (P.h₀ h_rep.2))
        (P.h₀ (Quotient.out x).2)) D₁.eql.choose.2⟩ = x₀ then (1 : ℤ) else 0) =
    (if x₀ ∈ smulOrbit P D₁ j then (1 : ℤ) else 0) := by
    have h_mk (q : decompQuot P D₁) : M_mk P ⟨(β : G) * ↑h_rep * ↑q.out * g₁,
        Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ β.2 (P.h₀ h_rep.2))
          (P.h₀ q.out.2)) D₁.eql.choose.2⟩ =
      M_mk P ⟨γ * ↑q.out * g₁,
        delta_mul_mem P.H P.Δ q.out j.eql.choose D₁.eql.choose P.h₀⟩ :=
      congr_arg (M_mk P) (Subtype.ext (congrArg (· * ↑q.out * g₁) h_eq_γ))
    by_cases hmem : x₀ ∈ smulOrbit P D₁ j
    · rw [if_pos hmem]
      simp only [smulOrbit, Finset.mem_image] at hmem
      obtain ⟨q₀, _, hq₀⟩ := hmem
      rw [Finset.sum_eq_single q₀]
      · exact if_pos ((h_mk q₀).symm ▸ hq₀)
      · intro q _ hne; exact if_neg fun heq =>
          hne (smulOrbit_map_injective P D₁ j ((h_mk q).symm.trans heq |>.trans hq₀.symm))
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [if_neg hmem]
      exact Finset.sum_eq_zero fun q _ => if_neg fun heq =>
        hmem (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, (h_mk q).symm.trans heq⟩)
  rwa [h_lhs_eq] at h_pt

private lemma smulOrbit_count_eq_m' (D₂ D₁ D₀ : T' P) (m₀ x₀ : M P)
    (hx₀ : x₀ ∈ smulOrbit P D₀ m₀) :
    (∑ j ∈ smulOrbit P D₂ m₀, if x₀ ∈ smulOrbit P D₁ j then (1 : ℤ) else 0) =
    (m P D₂ D₁) D₀ := by
  simp only [smulOrbit, Finset.mem_image] at hx₀
  obtain ⟨q₀, _, hq₀⟩ := hx₀
  rw [smulOrbit, Finset.sum_image (fun a _ b _ hab => smulOrbit_map_injective P D₂ m₀ hab)]
  simp_rw [smulOrbit_indicator_eq_sum P D₁ m₀ x₀]
  have M_mk_eq_iff : ∀ (a b : P.Δ),
      M_mk P a = M_mk P b ↔ ({(a : G)} : Set G) * ↑P.H = {(b : G)} * ↑P.H :=
    fun a b => ⟨fun h => congr_arg M.set h, fun h => M_ext_set P _ _ h⟩
  simp_rw [← hq₀, M_mk_eq_iff]
  rw [show (⊤ : Finset (decompQuot P D₂)) = Finset.univ from rfl]
  rw [← Fintype.sum_prod_type']
  rw [Finset.sum_boole, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have h_iff : ∀ (p : decompQuot P D₂ × decompQuot P D₁),
      ({(m₀.eql.choose : G) * ↑p.1.out * (D₂.eql.choose : G) * ↑p.2.out *
        (D₁.eql.choose : G)} : Set G) * ↑P.H =
        {(m₀.eql.choose : G) * ↑q₀.out * (D₀.eql.choose : G)} * ↑P.H ↔
      ({(↑p.1.out : G) * (D₂.eql.choose : G)} : Set G) *
        {(↑p.2.out : G) * (D₁.eql.choose : G)} * ↑P.H =
        {(↑q₀.out : G) * (D₀.eql.choose : G)} * ↑P.H := by
    intro p
    constructor
    · intro h
      have hl : ({(m₀.eql.choose : G) * ↑p.1.out * (D₂.eql.choose : G) * ↑p.2.out *
          (D₁.eql.choose : G)} : Set G) =
          ({(m₀.eql.choose : G)} : Set G) *
          {↑p.1.out * (D₂.eql.choose : G) * (↑p.2.out * (D₁.eql.choose : G))} := by
        rw [Set.singleton_mul_singleton]; congr 1; group
      have hr : ({(m₀.eql.choose : G) * ↑q₀.out * (D₀.eql.choose : G)} : Set G) =
          ({(m₀.eql.choose : G)} : Set G) * {↑q₀.out * (D₀.eql.choose : G)} := by
        rw [Set.singleton_mul_singleton]; congr 1; group
      have hset' : ({(m₀.eql.choose : G)} : Set G) *
          ({↑p.1.out * (D₂.eql.choose : G) * (↑p.2.out * (D₁.eql.choose : G))} * ↑P.H) =
          {(m₀.eql.choose : G)} * ({↑q₀.out * (D₀.eql.choose : G)} * ↑P.H) := by
        rw [← mul_assoc, ← hl, ← mul_assoc, ← hr]; exact h
      have h' := set_singleton_mul_left_cancel (m₀.eql.choose : G) hset'
      rwa [Set.singleton_mul_singleton]
    · intro h
      rw [Set.singleton_mul_singleton] at h
      have hl : ({(m₀.eql.choose : G) * ↑p.1.out * (D₂.eql.choose : G) * ↑p.2.out *
          (D₁.eql.choose : G)} : Set G) =
          ({(m₀.eql.choose : G)} : Set G) *
          {↑p.1.out * (D₂.eql.choose : G) * (↑p.2.out * (D₁.eql.choose : G))} := by
        rw [Set.singleton_mul_singleton]; congr 1; group
      have hr : ({(m₀.eql.choose : G) * ↑q₀.out * (D₀.eql.choose : G)} : Set G) =
          ({(m₀.eql.choose : G)} : Set G) * {↑q₀.out * (D₀.eql.choose : G)} := by
        rw [Set.singleton_mul_singleton]; congr 1; group
      calc ({(m₀.eql.choose : G) * ↑p.1.out * (D₂.eql.choose : G) * ↑p.2.out *
              (D₁.eql.choose : G)} : Set G) * ↑P.H
          _ = ({(m₀.eql.choose : G)} * {↑p.1.out * (D₂.eql.choose : G) *
              (↑p.2.out * (D₁.eql.choose : G))}) * ↑P.H := by rw [hl]
          _ = {(m₀.eql.choose : G)} * ({↑p.1.out * (D₂.eql.choose : G) *
              (↑p.2.out * (D₁.eql.choose : G))} * ↑P.H) :=
              mul_assoc ({(m₀.eql.choose : G)} : Set G) _ _
          _ = {(m₀.eql.choose : G)} * ({↑q₀.out * (D₀.eql.choose : G)} * ↑P.H) :=
              congr_arg _ h
          _ = ({(m₀.eql.choose : G)} * {↑q₀.out * (D₀.eql.choose : G)}) * ↑P.H :=
              (mul_assoc ({(m₀.eql.choose : G)} : Set G) _ _).symm
          _ = ({(m₀.eql.choose : G) * ↑q₀.out * (D₀.eql.choose : G)} : Set G) * ↑P.H := by
              rw [hr]
  have h_prop := fun p => propext (h_iff p)
  simp_rw [h_prop]
  rw [show (m P D₂ D₁) D₀ = (m' P D₂ D₁ D₀ : ℤ) from rfl]
  unfold m'
  norm_cast
  exact m'_uniform P D₂ D₁ D₀ q₀

private lemma smul_assoc_key (D₁ D₂ : T' P) (m₀ : M P) :
    ((m P D₂ D₁).sum fun D b₁ ↦ ∑ i ∈ smulOrbit P D m₀, Finsupp.single i (b₁ * 1)) =
    (∑ j ∈ smulOrbit P D₂ m₀, Finsupp.single j 1).sum
      fun m b₂ ↦ ∑ i ∈ smulOrbit P D₁ m, Finsupp.single i (1 * b₂) := by
  simp only [mul_one, one_mul]
  ext x₀
  simp only [Finsupp.sum_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp_rw [Finset.sum_ite_eq']
  have h_rhs : (∑ j ∈ smulOrbit P D₂ m₀, Finsupp.single j 1).sum
      (fun a₁ b ↦ if x₀ ∈ smulOrbit P D₁ a₁ then b else (0 : ℤ)) =
      ∑ j ∈ smulOrbit P D₂ m₀, if x₀ ∈ smulOrbit P D₁ j then 1 else 0 := by
    rw [← Finsupp.sum_finset_sum_index
      (h_zero := fun a => by simp)
      (h_add := fun a b₁ b₂ => by split_ifs <;> simp [*])]
    congr 1; ext j
    exact Finsupp.sum_single_index (by simp)
  rw [h_rhs]
  by_cases h_ex : ∃ D₀ ∈ (m P D₂ D₁).support, x₀ ∈ smulOrbit P D₀ m₀
  · obtain ⟨D₀, hD₀, hx₀⟩ := h_ex
    have h_lhs : (m P D₂ D₁).sum (fun a₁ b ↦
        if x₀ ∈ smulOrbit P a₁ m₀ then b
        else (0 : ℤ)) = (m P D₂ D₁) D₀ := by
      rw [Finsupp.sum]
      rw [Finset.sum_eq_single D₀
        (fun D hD hne => if_neg (Finset.disjoint_left.mp
          (smulOrbit_disjoint_of_ne P D₀ D m₀ hne.symm) hx₀))
        (fun h => absurd hD₀ h)]
      exact if_pos hx₀
    rw [h_lhs]
    exact (smulOrbit_count_eq_m' P D₂ D₁ D₀ m₀ x₀ hx₀).symm
  · push_neg at h_ex
    have h_lhs : (m P D₂ D₁).sum (fun a₁ b ↦
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
          P D₂ D₁ m₀ j x₀ hj hmem
      exact absurd hD_mem (h_ex D hD)).symm

private lemma smul_assoc_singles (D₁ D₂ : T' P) (a₁ a₂ : ℤ) (m₀ : M P) (c₀ : ℤ) :
    (T_single P ℤ D₂ a₂ * T_single P ℤ D₁ a₁) • (M_single P ℤ m₀ c₀) =
    T_single P ℤ D₁ a₁ • (T_single P ℤ D₂ a₂ • M_single P ℤ m₀ c₀) := by
  rw [𝕋_mul_singleton, single_smul_single]
  simp only [smul_eq_sum, M_single, T_single]
  have hsi : ∀ (D : T' P) (b : ℤ),
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
  have h_lhs : (a₂ • a₁ • m P D₂ D₁).sum
      (fun D b₁ ↦ if x₀ ∈ smulOrbit P D m₀ then b₁ * c₀ else (0 : ℤ)) =
      (m P D₂ D₁).sum
      (fun D b₁ ↦
        if x₀ ∈ smulOrbit P D m₀
        then a₂ * (a₁ * b₁) * c₀
        else (0 : ℤ)) := by
    rw [show a₂ • a₁ • m P D₂ D₁ = a₂ • (a₁ • m P D₂ D₁) from rfl]
    rw [Finsupp.sum_smul_index (fun i => by split_ifs <;> simp)]
    rw [Finsupp.sum_smul_index (fun i => by split_ifs <;> simp)]
  rw [h_lhs]
  have key := smul_assoc_key P D₁ D₂ m₀
  simp only [mul_one, one_mul] at key
  have key_pt := congr_fun (congr_arg DFunLike.coe key) x₀
  simp only [Finsupp.sum_apply, Finsupp.finset_sum_apply, Finsupp.single_apply] at key_pt
  simp_rw [Finset.sum_ite_eq'] at key_pt
  simp_rw [show ∀ (D : T' P) (b₁ : ℤ),
      (if x₀ ∈ smulOrbit P D m₀ then a₂ * (a₁ * b₁) * c₀ else 0) =
      a₁ * a₂ * c₀ * (if x₀ ∈ smulOrbit P D m₀ then b₁ else 0) from
    fun D b₁ => by split_ifs <;> ring]
  simp_rw [show ∀ (j : M P),
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

noncomputable instance instIsScalarTower :
    IsScalarTower (𝕋 P ℤ) (𝕋 P ℤ) (𝕄 P ℤ) where
  smul_assoc x y z := by
    simp only [smul_def]
    induction x using Finsupp.induction_linear with
    | zero => simp only [mul_zero, zero_smul_𝕄]
    | add x₁ x₂ ih₁ ih₂ =>
      rw [mul_add, smul_add_left, ih₁, ih₂, ← smul_add_left]
    | single D₁ a₁ =>
      induction y using Finsupp.induction_linear with
      | zero => simp only [zero_mul, zero_smul_𝕄, smul_zero_𝕄]
      | add y₁ y₂ ih₁ ih₂ =>
        rw [add_mul, smul_add_left, ih₁, ih₂, smul_add_left, smul_add_right]
      | single D₂ a₂ =>
        induction z using Finsupp.induction_linear with
        | zero => simp only [smul_zero_𝕄]
        | add z₁ z₂ ih₁ ih₂ =>
          rw [smul_add_right, smul_add_right, ih₁, ih₂, smul_add_right]
        | single m₀ c₀ =>
          exact smul_assoc_singles P D₁ D₂ a₁ a₂ m₀ c₀
