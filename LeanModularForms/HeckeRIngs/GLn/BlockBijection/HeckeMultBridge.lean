/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.BlockBijection.BlockEmbed

/-!
# Block Embedding Bijection: lattice model and rep ↔ diagMat bridge

The intermediate-lattice model for `heckeMultiplicity` and the bridge between
`rep (T_diag a)` and `diagMat_delta` multiplicities, plus the diagMat-level `≥`
direction `heckeMultiplicity_block_embed_ge_diagMat` (Shimura §3.2, Lemma 3.19).
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset
open Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable {m : ℕ} [NeZero m]

private def IntLattice (n : ℕ) [NeZero n] (d : Fin n → ℕ) (_ : ∀ i, 0 < d i) :=
  decompQuot (GL_pair n) (diagMat_delta n d)

private lemma conjAct_inv_mem_of_subgroupOf {n : ℕ} [NeZero n] (g : GL (Fin n) ℚ)
    (m : (ConjAct.toConjAct g • (GL_pair n).H).subgroupOf (GL_pair n).H) :
    g⁻¹ * (m : GL (Fin n) ℚ)⁻¹ * g ∈ (GL_pair n).H := by
  have hm := m.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hm
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hm
  have := (GL_pair n).H.inv_mem hm; convert this using 1; group

private lemma conjAct_mem_of_subgroupOf {n : ℕ} [NeZero n] (g : GL (Fin n) ℚ)
    (m : (ConjAct.toConjAct g • (GL_pair n).H).subgroupOf (GL_pair n).H) :
    g⁻¹ * (m : GL (Fin n) ℚ) * g ∈ (GL_pair n).H := by
  have hm := m.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hm
  simpa [ConjAct.ofConjAct_toConjAct] using hm

private lemma mk_out_coe_eq_mul {n : ℕ} [NeZero n] {g : GL (Fin n) ℚ} {h : (GL_pair n).H}
    {m : (ConjAct.toConjAct g • (GL_pair n).H).subgroupOf (GL_pair n).H}
    (hn_eq : (⟦h⟧ : (GL_pair n).H ⧸
        (ConjAct.toConjAct g • (GL_pair n).H).subgroupOf (GL_pair n).H).out = h * m) :
    (((⟦h⟧ : (GL_pair n).H ⧸
        (ConjAct.toConjAct g • (GL_pair n).H).subgroupOf (GL_pair n).H).out : (GL_pair n).H) :
      GL (Fin n) ℚ) = (h : GL (Fin n) ℚ) * (m : GL (Fin n) ℚ) := by
  have := congr_arg (Subtype.val : ↥(GL_pair n).H → GL (Fin n) ℚ) hn_eq
  simpa [Subgroup.coe_mul] using this

/-- `q = 1` specialization of `Associativity.coset_shift_fwd`: shift the underlying
representatives `(a, b) ↦ (a · n₁, gA⁻¹ · n₁⁻¹ · gA · b · n₂)` while keeping the
target right-coset `{gC} · H` fixed. -/
lemma coset_shift_fwd_q1 {n : ℕ} [NeZero n]
    (a b a' b' gA gB gC n₁ n₂ : GL (Fin n) ℚ)
    (hcond : ({a * gA * (b * gB)} : Set _) * ((GL_pair n).H : Set _) =
      {gC} * ((GL_pair n).H : Set _))
    (ha' : a' = a * n₁)
    (hb' : b' = gA⁻¹ * n₁⁻¹ * gA * b * n₂)
    (hn₂_conj : gB⁻¹ * n₂ * gB ∈ (GL_pair n).H) :
    ({a' * gA * (b' * gB)} : Set _) * ((GL_pair n).H : Set _) =
      {gC} * ((GL_pair n).H : Set _) := by
  subst ha' hb'
  apply leftCoset_eq_of_not_disjoint
  rw [Set.not_disjoint_iff]
  refine ⟨a * n₁ * gA * (gA⁻¹ * n₁⁻¹ * gA * b * n₂ * gB),
    ⟨1, (GL_pair n).H.one_mem, by simp [smul_eq_mul]⟩, ?_⟩
  have hmem : a * gA * (b * gB) ∈ ({gC} : Set _) * ((GL_pair n).H : Set _) := by
    rw [← hcond]; exact ⟨_, rfl, 1, (GL_pair n).H.one_mem, by group⟩
  obtain ⟨y, h_eq, h₀, hh₀, hprod⟩ := hmem
  rw [Set.mem_singleton_iff] at h_eq
  rw [h_eq] at hprod
  refine ⟨h₀ * (gB⁻¹ * n₂ * gB), (GL_pair n).H.mul_mem hh₀ hn₂_conj, ?_⟩
  simp only [smul_eq_mul]; symm
  calc a * n₁ * gA * (gA⁻¹ * n₁⁻¹ * gA * b * n₂ * gB)
      = (a * gA * (b * gB)) * (gB⁻¹ * n₂ * gB) := by group
    _ = gC * (h₀ * (gB⁻¹ * n₂ * gB)) := by
        simp only at hprod
        rw [← hprod]; group

private lemma decompQuot_left_mul_cancel {n : ℕ} [NeZero n]
    (g : (GL_pair n).Δ) (h x y : (GL_pair n).H)
    (heq : (⟦h * x⟧ : decompQuot (GL_pair n) g) = ⟦h * y⟧) :
    (⟦x⟧ : decompQuot (GL_pair n) g) = ⟦y⟧ := by
  rw [Quotient.eq, QuotientGroup.leftRel_apply] at heq ⊢
  convert heq using 1
  rw [show (h * x)⁻¹ * (h * y) = x⁻¹ * y by group]

private lemma decompQuot_out_eq {n : ℕ} [NeZero n] {g : (GL_pair n).Δ}
    (q : decompQuot (GL_pair n) g) :
    (⟦q.out⟧ : decompQuot (GL_pair n) g) = q := Quotient.out_eq q

private lemma decompQuot_eq_of_out_eq {n : ℕ} [NeZero n] {g : (GL_pair n).Δ}
    {q₁ q₂ : decompQuot (GL_pair n) g}
    (h : (⟦q₁.out⟧ : decompQuot (GL_pair n) g) = ⟦q₂.out⟧) : q₁ = q₂ := by
  rw [decompQuot_out_eq, decompQuot_out_eq] at h; exact h

private lemma decompQuot_eq_of_inv_out_mul_mem {n : ℕ} [NeZero n] {g : (GL_pair n).Δ}
    {q₁ q₂ : decompQuot (GL_pair n) g}
    (h : (q₁.out)⁻¹ * q₂.out ∈
      (ConjAct.toConjAct (g : GL (Fin n) ℚ) • (GL_pair n).H).subgroupOf (GL_pair n).H) :
    q₁ = q₂ :=
  decompQuot_eq_of_out_eq (Quotient.sound ((QuotientGroup.leftRel_apply).mpr h))

private lemma decompQuot_out_coe_eq_mul {n : ℕ} [NeZero n] {δ : (GL_pair n).Δ}
    {h : (GL_pair n).H}
    {m : (ConjAct.toConjAct (δ : GL (Fin n) ℚ) • (GL_pair n).H).subgroupOf (GL_pair n).H}
    (hm : (⟦h⟧ : decompQuot (GL_pair n) δ).out = h * m) :
    ((⟦h⟧ : decompQuot (GL_pair n) δ).out : GL (Fin n) ℚ) =
      (h : GL (Fin n) ℚ) * (m : GL (Fin n) ℚ) := by
  have := congr_arg (Subtype.val : ↥(GL_pair n).H → GL (Fin n) ℚ) hm
  simpa [Subgroup.coe_mul] using this

private noncomputable def outShift {n : ℕ} [NeZero n] (δ : (GL_pair n).Δ)
    (σ : (GL_pair n).H) :
    (ConjAct.toConjAct (δ : GL (Fin n) ℚ) • (GL_pair n).H).subgroupOf (GL_pair n).H :=
  (QuotientGroup.mk_out_eq_mul _ σ).choose

private lemma out_eq_mul_outShift {n : ℕ} [NeZero n] (δ : (GL_pair n).Δ) (σ : (GL_pair n).H) :
    (⟦σ⟧ : decompQuot (GL_pair n) δ).out = σ * outShift δ σ :=
  (QuotientGroup.mk_out_eq_mul _ σ).choose_spec

private noncomputable def compensatedYbase {n : ℕ} [NeZero n] (δ : (GL_pair n).Δ)
    (σ τ : (GL_pair n).H) : (GL_pair n).H :=
  ⟨_, conjAct_inv_mem_of_subgroupOf (δ : GL (Fin n) ℚ) (outShift δ σ)⟩ * τ

private lemma compensatedYbase_coe {n : ℕ} [NeZero n] (δ : (GL_pair n).Δ)
    (σ τ : (GL_pair n).H) :
    ((compensatedYbase δ σ τ : (GL_pair n).H) : GL (Fin n) ℚ) =
      (δ : GL (Fin n) ℚ)⁻¹ * ((outShift δ σ : (GL_pair n).H) : GL (Fin n) ℚ)⁻¹ *
        (δ : GL (Fin n) ℚ) * (τ : GL (Fin n) ℚ) := by
  simp [compensatedYbase, Subgroup.coe_mul]

private lemma coset_cond_of_compensated_out {n : ℕ} [NeZero n] (δA δB δC : (GL_pair n).Δ)
    (σ_bar τ_bar : (GL_pair n).H)
    (h_rc_lift_merged :
        ({(σ_bar : GL (Fin n) ℚ) * (δA : GL (Fin n) ℚ) *
            ((τ_bar : GL (Fin n) ℚ) * (δB : GL (Fin n) ℚ))} : Set _) *
          ((GL_pair n).H : Set _) =
        {(δC : GL (Fin n) ℚ)} * ((GL_pair n).H : Set _)) :
    ({((⟦σ_bar⟧ : decompQuot (GL_pair n) δA).out : GL (Fin n) ℚ) * (δA : GL (Fin n) ℚ)} :
        Set _) *
      {((⟦compensatedYbase δA σ_bar τ_bar⟧ : decompQuot (GL_pair n) δB).out :
          GL (Fin n) ℚ) * (δB : GL (Fin n) ℚ)} *
      ((GL_pair n).H : Set _) =
      {(δC : GL (Fin n) ℚ)} * ((GL_pair n).H : Set _) := by
  set n₁ := outShift δA σ_bar
  obtain ⟨n₂, hn₂_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (δB : GL (Fin n) ℚ) • (GL_pair n).H).subgroupOf (GL_pair n).H)
    (compensatedYbase δA σ_bar τ_bar)
  have hj_form : ((⟦compensatedYbase δA σ_bar τ_bar⟧ :
        decompQuot (GL_pair n) δB).out : GL (Fin n) ℚ) =
      (δA : GL (Fin n) ℚ)⁻¹ * (n₁ : GL (Fin n) ℚ)⁻¹ * (δA : GL (Fin n) ℚ) *
        (τ_bar : GL (Fin n) ℚ) * (n₂ : GL (Fin n) ℚ) := by
    rw [decompQuot_out_coe_eq_mul hn₂_eq, compensatedYbase_coe]
  have hn₂_conj : (δB : GL (Fin n) ℚ)⁻¹ * (n₂ : GL (Fin n) ℚ) * (δB : GL (Fin n) ℚ) ∈
      (GL_pair n).H := conjAct_mem_of_subgroupOf _ n₂
  have h_target := coset_shift_fwd_q1 (σ_bar : GL (Fin n) ℚ) (τ_bar : GL (Fin n) ℚ)
    ((⟦σ_bar⟧ : decompQuot (GL_pair n) δA).out : GL (Fin n) ℚ)
    ((⟦compensatedYbase δA σ_bar τ_bar⟧ : decompQuot (GL_pair n) δB).out : GL (Fin n) ℚ)
    (δA : GL (Fin n) ℚ) (δB : GL (Fin n) ℚ) (δC : GL (Fin n) ℚ)
    (n₁ : GL (Fin n) ℚ) (n₂ : GL (Fin n) ℚ)
    h_rc_lift_merged (decompQuot_out_coe_eq_mul (out_eq_mul_outShift δA σ_bar)) hj_form
    hn₂_conj
  rw [← Set.singleton_mul_singleton] at h_target
  exact h_target

/-- Diagonal-level `≥` direction of `heckeMultiplicity_block_embed`. -/
lemma heckeMultiplicity_block_embed_ge_diagMat {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ≤
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) := by
  have hcons_a := cons_one_pos ha
  have hcons_b := cons_one_pos hb
  have hcons_c := cons_one_pos hc
  have h_dval_a : ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
      GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 a) :=
    diagMat_delta_val (k + 2) (Fin.cons 1 a) hcons_a
  have h_dval_b : ((diagMat_delta (k + 2) (Fin.cons 1 b) : (GL_pair (k + 2)).Δ) :
      GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 b) :=
    diagMat_delta_val (k + 2) (Fin.cons 1 b) hcons_b
  have h_dval_c : ((diagMat_delta (k + 2) (Fin.cons 1 c) : (GL_pair (k + 2)).Δ) :
      GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 c) :=
    diagMat_delta_val (k + 2) (Fin.cons 1 c) hcons_c
  have h_dval_a1 : ((diagMat_delta (k + 1) a : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) a := diagMat_delta_val (k + 1) a ha
  have h_dval_b1 : ((diagMat_delta (k + 1) b : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) b := diagMat_delta_val (k + 1) b hb
  have h_dval_c1 : ((diagMat_delta (k + 1) c : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) c := diagMat_delta_val (k + 1) c hc
  let dA : (GL_pair (k + 2)).Δ := diagMat_delta (k + 2) (Fin.cons 1 a)
  let SrcType : Type := {p : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a) ×
            decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b) |
            ({(p.1.out : GL (Fin (k + 1)) ℚ) *
              (diagMat_delta (k + 1) a : GL (Fin (k + 1)) ℚ)} : Set _) *
            {(p.2.out : GL (Fin (k + 1)) ℚ) *
              (diagMat_delta (k + 1) b : GL (Fin (k + 1)) ℚ)} *
            ((GL_pair (k + 1)).H : Set _) =
            {(diagMat_delta (k + 1) c : GL (Fin (k + 1)) ℚ)} *
              ((GL_pair (k + 1)).H : Set _)}
  let TgtType : Type := {p : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)) ×
            decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)) |
            ({(p.1.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
            {(p.2.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
            ((GL_pair (k + 2)).H : Set _) =
            {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
              ((GL_pair (k + 2)).H : Set _)}
  let f : SrcType → TgtType := fun ⟨⟨i, j⟩, hcond⟩ ↦
    ⟨(⟦slSuccEmbed_H i.out⟧,
      ⟦compensatedYbase dA (slSuccEmbed_H i.out) (slSuccEmbed_H j.out)⟧),
      by
        have h_iff := fiber_diagMat_iff_mem_H a b c ha hb hc i.out j.out
        rw [← h_dval_a1, ← h_dval_b1, ← h_dval_c1] at h_iff
        have h_mem_pre := h_iff.mp hcond
        have h_mem : (diagMat (k + 1) c)⁻¹ * (i.out : GL (Fin (k + 1)) ℚ) *
            diagMat (k + 1) a * (j.out : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) b ∈
              (GL_pair (k + 1)).H := by
          convert h_mem_pre using 2 <;> simp [h_dval_a1, h_dval_b1, h_dval_c1]
        have h_mem' := slSuccEmbed_H_fiber_transfer a b c ha hb hc i.out j.out h_mem
        have h_iff_lift := fiber_diagMat_iff_mem_H (Fin.cons 1 a) (Fin.cons 1 b)
          (Fin.cons 1 c) hcons_a hcons_b hcons_c
          (slSuccEmbed_H i.out) (slSuccEmbed_H j.out)
        have h_rc_lift := h_iff_lift.mpr h_mem'
        rw [← h_dval_a, ← h_dval_b, ← h_dval_c] at h_rc_lift
        exact coset_cond_of_compensated_out dA (diagMat_delta (k + 2) (Fin.cons 1 b))
          (diagMat_delta (k + 2) (Fin.cons 1 c)) (slSuccEmbed_H i.out) (slSuccEmbed_H j.out)
          (by rw [← Set.singleton_mul_singleton]; exact h_rc_lift)⟩
  simp only [HeckeRing.heckeMultiplicity]
  norm_cast
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨⟨i₁, j₁⟩, _⟩ ⟨⟨i₂, j₂⟩, _⟩ heq
  have heq_pair := Subtype.mk.inj heq
  have h_i_eq : (⟦slSuccEmbed_H i₁.out⟧ :
      decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a))) =
      ⟦slSuccEmbed_H i₂.out⟧ := (Prod.mk.injEq _ _ _ _).mp heq_pair |>.1
  have h_j_eq : (⟦compensatedYbase dA (slSuccEmbed_H i₁.out) (slSuccEmbed_H j₁.out)⟧ :
      decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) =
      ⟦compensatedYbase dA (slSuccEmbed_H i₂.out) (slSuccEmbed_H j₂.out)⟧ :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.2
  have h_i_final : i₁ = i₂ :=
    decompQuot_eq_of_out_eq (decompQuot_slSuccEmbed_diagMat_injective a ha h_i_eq)
  subst h_i_final
  have h_j_cancel := decompQuot_left_mul_cancel
    (diagMat_delta (k + 2) (Fin.cons 1 b))
    ⟨_, conjAct_inv_mem_of_subgroupOf (dA : GL (Fin (k + 2)) ℚ)
      (outShift dA (slSuccEmbed_H i₁.out))⟩
    (slSuccEmbed_H j₁.out) (slSuccEmbed_H j₂.out) h_j_eq
  have h_j_final : j₁ = j₂ :=
    decompQuot_eq_of_out_eq (decompQuot_slSuccEmbed_diagMat_injective b hb h_j_cancel)
  subst h_j_final
  rfl

private lemma rep_stab_iff_diag_stab {n : ℕ} [NeZero n]
    (a : Fin n → ℕ) (_ : ∀ i, 0 < a i)
    (La Ra : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) =
      (La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))
    (σ : (GL_pair n).H) :
    σ ∈ (ConjAct.toConjAct (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H ↔
    (⟨(La : GL (Fin n) ℚ)⁻¹ * σ * (La : GL (Fin n) ℚ),
        (GL_pair n).H.mul_mem ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem La.2) σ.2)
          La.2⟩ : (GL_pair n).H) ∈
      (ConjAct.toConjAct (diagMat n a : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H := by
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [hLR]
  constructor
  · intro hmem
    have h1 : (Ra : GL (Fin n) ℚ) *
        (((La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))⁻¹ *
          (σ : GL (Fin n) ℚ) *
          ((La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))) *
        (Ra : GL (Fin n) ℚ)⁻¹ ∈ (GL_pair n).H :=
      (GL_pair n).H.mul_mem ((GL_pair n).H.mul_mem Ra.2 hmem) ((GL_pair n).H.inv_mem Ra.2)
    convert h1 using 1; group
  · intro hmem
    have h1 : (Ra : GL (Fin n) ℚ)⁻¹ *
        ((diagMat n a)⁻¹ * ((La : GL (Fin n) ℚ)⁻¹ * (σ : GL (Fin n) ℚ) *
          (La : GL (Fin n) ℚ)) * diagMat n a) *
        (Ra : GL (Fin n) ℚ) ∈ (GL_pair n).H :=
      (GL_pair n).H.mul_mem ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem Ra.2) hmem) Ra.2
    convert h1 using 1; group

private lemma rep_stab_iff_diag_stab' {n : ℕ} [NeZero n]
    (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (Lb Rb : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) =
      (Lb : GL (Fin n) ℚ) * diagMat n b * (Rb : GL (Fin n) ℚ))
    (τ : (GL_pair n).H) :
    τ ∈ (ConjAct.toConjAct (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H ↔
    (⟨(Lb : GL (Fin n) ℚ)⁻¹ * τ * (Lb : GL (Fin n) ℚ),
        (GL_pair n).H.mul_mem ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem Lb.2) τ.2)
          Lb.2⟩ : (GL_pair n).H) ∈
      (ConjAct.toConjAct (diagMat n b : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H :=
  rep_stab_iff_diag_stab b hb Lb Rb hLR τ

private lemma decompQuot_asymm_first_wd_rev {n : ℕ} [NeZero n]
    (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (La Ra Lc : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) =
      (La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))
    (σ'₁ σ'₂ : (GL_pair n).H)
    (hrel : QuotientGroup.leftRel
      ((ConjAct.toConjAct (diagMat_delta n a : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H) σ'₁ σ'₂) :
    QuotientGroup.leftRel
      ((ConjAct.toConjAct (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H)
      (Lc * σ'₁ * La⁻¹) (Lc * σ'₂ * La⁻¹) := by
  rw [QuotientGroup.leftRel_apply] at hrel ⊢
  rw [diagMat_delta_val n a ha] at hrel
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hrel ⊢
  rw [hLR]
  have := (GL_pair n).H.mul_mem
    ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem Ra.2) hrel) Ra.2
  convert this using 1
  push_cast
  group

private lemma decompQuot_asymm_second_wd_rev {n : ℕ} [NeZero n]
    (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (Lb Rb Ra : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) =
      (Lb : GL (Fin n) ℚ) * diagMat n b * (Rb : GL (Fin n) ℚ))
    (τ'₁ τ'₂ : (GL_pair n).H)
    (hrel : QuotientGroup.leftRel
      ((ConjAct.toConjAct (diagMat_delta n b : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H) τ'₁ τ'₂) :
    QuotientGroup.leftRel
      ((ConjAct.toConjAct (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H)
      (Ra⁻¹ * τ'₁ * Lb⁻¹) (Ra⁻¹ * τ'₂ * Lb⁻¹) := by
  rw [QuotientGroup.leftRel_apply] at hrel ⊢
  rw [diagMat_delta_val n b hb] at hrel
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hrel ⊢
  rw [hLR]
  have := (GL_pair n).H.mul_mem
    ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem Rb.2) hrel) Rb.2
  convert this using 1
  push_cast
  group

private lemma decompQuot_asymm_first_wd {n : ℕ} [NeZero n]
    (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (La Ra Lc : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) =
      (La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))
    (σ₁ σ₂ : (GL_pair n).H)
    (hrel : QuotientGroup.leftRel
      ((ConjAct.toConjAct (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H) σ₁ σ₂) :
    QuotientGroup.leftRel
      ((ConjAct.toConjAct (diagMat_delta n a : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H)
      (Lc⁻¹ * σ₁ * La) (Lc⁻¹ * σ₂ * La) := by
  rw [QuotientGroup.leftRel_apply] at hrel ⊢
  rw [diagMat_delta_val n a ha]
  have hsimp : (Lc⁻¹ * σ₁ * La)⁻¹ * (Lc⁻¹ * σ₂ * La) = La⁻¹ * (σ₁⁻¹ * σ₂) * La := by group
  rw [hsimp]
  have := (rep_stab_iff_diag_stab a ha La Ra hLR (σ₁⁻¹ * σ₂)).mp hrel
  convert this using 1

private lemma decompQuot_asymm_second_wd {n : ℕ} [NeZero n]
    (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (Lb Rb Ra : (GL_pair n).H)
    (hLR : (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) =
      (Lb : GL (Fin n) ℚ) * diagMat n b * (Rb : GL (Fin n) ℚ))
    (τ₁ τ₂ : (GL_pair n).H)
    (hrel : QuotientGroup.leftRel
      ((ConjAct.toConjAct (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H) τ₁ τ₂) :
    QuotientGroup.leftRel
      ((ConjAct.toConjAct (diagMat_delta n b : GL (Fin n) ℚ) •
        (GL_pair n).H).subgroupOf (GL_pair n).H)
      (Ra * τ₁ * Lb) (Ra * τ₂ * Lb) := by
  rw [QuotientGroup.leftRel_apply] at hrel ⊢
  rw [diagMat_delta_val n b hb]
  have hsimp : (Ra * τ₁ * Lb)⁻¹ * (Ra * τ₂ * Lb) = Lb⁻¹ * (τ₁⁻¹ * τ₂) * Lb := by group
  rw [hsimp]
  have := (rep_stab_iff_diag_stab b hb Lb Rb hLR (τ₁⁻¹ * τ₂)).mp hrel
  convert this using 1

private lemma rep_mem_H_iff_compensated_diag_mem_H {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ)
    (La Ra Lb Rb Lc Rc : (GL_pair n).H)
    (hDecA : (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) =
      (La : GL (Fin n) ℚ) * diagMat n a * (Ra : GL (Fin n) ℚ))
    (hDecB : (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) =
      (Lb : GL (Fin n) ℚ) * diagMat n b * (Rb : GL (Fin n) ℚ))
    (hDecC : (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ) =
      (Lc : GL (Fin n) ℚ) * diagMat n c * (Rc : GL (Fin n) ℚ))
    (σ τ : (GL_pair n).H) :
    ((HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ * σ *
      (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) * τ *
      (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) ∈ (GL_pair n).H) ↔
    ((diagMat n c)⁻¹ *
      ((Lc⁻¹ * σ * La : (GL_pair n).H) : GL (Fin n) ℚ) * diagMat n a *
      ((Ra * τ * Lb : (GL_pair n).H) : GL (Fin n) ℚ) * diagMat n b ∈ (GL_pair n).H) := by
  rw [hDecA, hDecB, hDecC]
  constructor
  · intro h
    have h1 := (GL_pair n).H.mul_mem
      ((GL_pair n).H.mul_mem Rc.2 h) ((GL_pair n).H.inv_mem Rb.2)
    convert h1 using 1
    push_cast
    group
  · intro h
    have h1 := (GL_pair n).H.mul_mem
      ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem Rc.2) h) Rb.2
    convert h1 using 1
    push_cast
    group

private lemma fiber_rep_iff_mem_H {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ)
    (σ τ : (GL_pair n).H) :
    (({(σ : GL (Fin n) ℚ) *
         (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ)} : Set _) *
        {(τ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ)} *
        ((GL_pair n).H : Set (GL (Fin n) ℚ)) =
        {(HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)} *
          ((GL_pair n).H : Set (GL (Fin n) ℚ))) ↔
    (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ * (σ : GL (Fin n) ℚ) *
        (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
        (τ : GL (Fin n) ℚ) *
        (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) ∈ (GL_pair n).H := by
  rw [Set.singleton_mul_singleton]
  constructor
  · intro h_eq
    have hmem : (σ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
        ((τ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ)) ∈
        ({(HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)} : Set _) *
          ((GL_pair n).H : Set (GL (Fin n) ℚ)) := by
      rw [← h_eq]; exact ⟨_, rfl, 1, (GL_pair n).H.one_mem, by simp⟩
    obtain ⟨_, hd_eq, h, hh, hprod⟩ := hmem
    rw [Set.mem_singleton_iff] at hd_eq
    subst hd_eq
    simp only at hprod
    have h_eq_factor : (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ *
        ((σ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
          ((τ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ))) = h := by
      rw [← hprod]; group
    rw [show (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ * (σ : GL (Fin n) ℚ) *
          (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) * (τ : GL (Fin n) ℚ) *
          (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) =
        (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ *
          ((σ : GL (Fin n) ℚ) * (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
            ((τ : GL (Fin n) ℚ) *
              (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ))) by group, h_eq_factor]
    exact hh
  · intro h_mem
    set h_elt := (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ * (σ : GL (Fin n) ℚ) *
        (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) * (τ : GL (Fin n) ℚ) *
        (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ)
    ext y
    constructor
    · rintro ⟨_, rfl, k, hk, rfl⟩
      refine ⟨_, rfl, h_elt * k, (GL_pair n).H.mul_mem h_mem hk, ?_⟩
      simp only [h_elt]; group
    · rintro ⟨_, rfl, k, hk, rfl⟩
      refine ⟨_, rfl, h_elt⁻¹ * k,
        (GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem h_mem) hk, ?_⟩
      simp only [h_elt]; group

private lemma heckeMultiplicity_rep_le_diagMat_delta {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) :
    HeckeRing.heckeMultiplicity (GL_pair n)
        (HeckeCoset.rep (T_diag a)) (HeckeCoset.rep (T_diag b))
        (HeckeCoset.rep (T_diag c)) ≤
    HeckeRing.heckeMultiplicity (GL_pair n)
        (diagMat_delta n a) (diagMat_delta n b) (diagMat_delta n c) := by
  obtain ⟨La_gl, hLa_mem, Ra_gl, hRa_mem, hDecA⟩ := T_diag_rep_decompose a ha
  obtain ⟨Lb_gl, hLb_mem, Rb_gl, hRb_mem, hDecB⟩ := T_diag_rep_decompose b hb
  obtain ⟨Lc_gl, hLc_mem, Rc_gl, hRc_mem, hDecC⟩ := T_diag_rep_decompose c hc
  set La : (GL_pair n).H := ⟨La_gl, hLa_mem⟩ with La_def
  set Ra : (GL_pair n).H := ⟨Ra_gl, hRa_mem⟩ with Ra_def
  set Lb : (GL_pair n).H := ⟨Lb_gl, hLb_mem⟩ with Lb_def
  set Rb : (GL_pair n).H := ⟨Rb_gl, hRb_mem⟩ with Rb_def
  set Lc : (GL_pair n).H := ⟨Lc_gl, hLc_mem⟩ with Lc_def
  set Rc : (GL_pair n).H := ⟨Rc_gl, hRc_mem⟩ with Rc_def
  have h_dval_a : ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n a :=
    diagMat_delta_val n a ha
  have h_dval_b : ((diagMat_delta n b : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n b :=
    diagMat_delta_val n b hb
  have h_dval_c : ((diagMat_delta n c : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n c :=
    diagMat_delta_val n c hc
  let dA : (GL_pair n).Δ := diagMat_delta n a
  let SrcType : Type := {p : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a)) ×
            decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b)) |
            ({(p.1.out : GL (Fin n) ℚ) *
              ((HeckeCoset.rep (T_diag a) : (GL_pair n).Δ) : GL (Fin n) ℚ)} : Set _) *
            {(p.2.out : GL (Fin n) ℚ) *
              ((HeckeCoset.rep (T_diag b) : (GL_pair n).Δ) : GL (Fin n) ℚ)} *
            ((GL_pair n).H : Set _) =
            {((HeckeCoset.rep (T_diag c) : (GL_pair n).Δ) : GL (Fin n) ℚ)} *
              ((GL_pair n).H : Set _)}
  let TgtType : Type := {p : decompQuot (GL_pair n) (diagMat_delta n a) ×
            decompQuot (GL_pair n) (diagMat_delta n b) |
            ({(p.1.out : GL (Fin n) ℚ) *
              (diagMat_delta n a : GL (Fin n) ℚ)} : Set _) *
            {(p.2.out : GL (Fin n) ℚ) *
              (diagMat_delta n b : GL (Fin n) ℚ)} *
            ((GL_pair n).H : Set _) =
            {(diagMat_delta n c : GL (Fin n) ℚ)} *
              ((GL_pair n).H : Set _)}
  let f : SrcType → TgtType := fun ⟨⟨i, j⟩, hcond⟩ ↦
    ⟨(⟦Lc⁻¹ * i.out * La⟧,
      ⟦compensatedYbase dA (Lc⁻¹ * i.out * La) (Ra * j.out * Lb)⟧),
      by
        have h_rep_mem := (fiber_rep_iff_mem_H a b c i.out j.out).mp hcond
        have h_diag_mem := (rep_mem_H_iff_compensated_diag_mem_H a b c
          La Ra Lb Rb Lc Rc hDecA hDecB hDecC i.out j.out).mp h_rep_mem
        have h_iff_lift := fiber_diagMat_iff_mem_H a b c ha hb hc
          (Lc⁻¹ * i.out * La) (Ra * j.out * Lb)
        have h_rc_lift := h_iff_lift.mpr h_diag_mem
        rw [← h_dval_a, ← h_dval_b, ← h_dval_c] at h_rc_lift
        exact coset_cond_of_compensated_out dA (diagMat_delta n b) (diagMat_delta n c)
          (Lc⁻¹ * i.out * La) (Ra * j.out * Lb)
          (by rw [← Set.singleton_mul_singleton]; exact h_rc_lift)⟩
  simp only [HeckeRing.heckeMultiplicity]
  norm_cast
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨⟨i₁, j₁⟩, _⟩ ⟨⟨i₂, j₂⟩, _⟩ heq
  have heq_pair := Subtype.mk.inj heq
  have h_i_eq : (⟦Lc⁻¹ * i₁.out * La⟧ :
      decompQuot (GL_pair n) (diagMat_delta n a)) =
      ⟦Lc⁻¹ * i₂.out * La⟧ := (Prod.mk.injEq _ _ _ _).mp heq_pair |>.1
  have h_j_eq : (⟦compensatedYbase dA (Lc⁻¹ * i₁.out * La) (Ra * j₁.out * Lb)⟧ :
      decompQuot (GL_pair n) (diagMat_delta n b)) =
      ⟦compensatedYbase dA (Lc⁻¹ * i₂.out * La) (Ra * j₂.out * Lb)⟧ :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.2
  have h_i_final : i₁ = i₂ := by
    rw [Quotient.eq] at h_i_eq
    change QuotientGroup.leftRel _ (Lc⁻¹ * i₁.out * La) (Lc⁻¹ * i₂.out * La) at h_i_eq
    refine decompQuot_eq_of_inv_out_mul_mem (g := HeckeCoset.rep (T_diag a)) ?_
    have h_rev := decompQuot_asymm_first_wd_rev (n := n) a ha La Ra Lc hDecA
      (Lc⁻¹ * i₁.out * La) (Lc⁻¹ * i₂.out * La) h_i_eq
    rw [QuotientGroup.leftRel_apply] at h_rev
    have h_simp : (Lc * (Lc⁻¹ * i₁.out * La) * La⁻¹)⁻¹ *
        (Lc * (Lc⁻¹ * i₂.out * La) * La⁻¹) = i₁.out⁻¹ * i₂.out := by group
    rwa [h_simp] at h_rev
  subst h_i_final
  have h_j_cancel := decompQuot_left_mul_cancel
    (diagMat_delta n b)
    ⟨_, conjAct_inv_mem_of_subgroupOf (dA : GL (Fin n) ℚ)
      (outShift dA (Lc⁻¹ * i₁.out * La))⟩
    (Ra * j₁.out * Lb) (Ra * j₂.out * Lb) h_j_eq
  have h_j_final : j₁ = j₂ := by
    rw [Quotient.eq] at h_j_cancel
    change QuotientGroup.leftRel _ (Ra * j₁.out * Lb) (Ra * j₂.out * Lb) at h_j_cancel
    refine decompQuot_eq_of_inv_out_mul_mem (g := HeckeCoset.rep (T_diag b)) ?_
    have h_rev := decompQuot_asymm_second_wd_rev (n := n) b hb Lb Rb Ra hDecB
      (Ra * j₁.out * Lb) (Ra * j₂.out * Lb) h_j_cancel
    rw [QuotientGroup.leftRel_apply] at h_rev
    have h_simp : (Ra⁻¹ * (Ra * j₁.out * Lb) * Lb⁻¹)⁻¹ *
        (Ra⁻¹ * (Ra * j₂.out * Lb) * Lb⁻¹) = j₁.out⁻¹ * j₂.out := by group
    rwa [h_simp] at h_rev
  subst h_j_final
  rfl

private lemma heckeMultiplicity_diagMat_le_rep_delta {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) :
    HeckeRing.heckeMultiplicity (GL_pair n)
        (diagMat_delta n a) (diagMat_delta n b) (diagMat_delta n c) ≤
    HeckeRing.heckeMultiplicity (GL_pair n)
        (HeckeCoset.rep (T_diag a)) (HeckeCoset.rep (T_diag b))
        (HeckeCoset.rep (T_diag c)) := by
  obtain ⟨La_gl, hLa_mem, Ra_gl, hRa_mem, hDecA⟩ := T_diag_rep_decompose a ha
  obtain ⟨Lb_gl, hLb_mem, Rb_gl, hRb_mem, hDecB⟩ := T_diag_rep_decompose b hb
  obtain ⟨Lc_gl, hLc_mem, Rc_gl, hRc_mem, hDecC⟩ := T_diag_rep_decompose c hc
  set La : (GL_pair n).H := ⟨La_gl, hLa_mem⟩ with La_def
  set Ra : (GL_pair n).H := ⟨Ra_gl, hRa_mem⟩ with Ra_def
  set Lb : (GL_pair n).H := ⟨Lb_gl, hLb_mem⟩ with Lb_def
  set Rb : (GL_pair n).H := ⟨Rb_gl, hRb_mem⟩ with Rb_def
  set Lc : (GL_pair n).H := ⟨Lc_gl, hLc_mem⟩ with Lc_def
  set Rc : (GL_pair n).H := ⟨Rc_gl, hRc_mem⟩ with Rc_def
  have h_dval_a : ((diagMat_delta n a : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n a :=
    diagMat_delta_val n a ha
  have h_dval_b : ((diagMat_delta n b : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n b :=
    diagMat_delta_val n b hb
  have h_dval_c : ((diagMat_delta n c : (GL_pair n).Δ) : GL (Fin n) ℚ) = diagMat n c :=
    diagMat_delta_val n c hc
  let dA : (GL_pair n).Δ := HeckeCoset.rep (T_diag a)
  let SrcType : Type := {p : decompQuot (GL_pair n) (diagMat_delta n a) ×
            decompQuot (GL_pair n) (diagMat_delta n b) |
            ({(p.1.out : GL (Fin n) ℚ) *
              (diagMat_delta n a : GL (Fin n) ℚ)} : Set _) *
            {(p.2.out : GL (Fin n) ℚ) *
              (diagMat_delta n b : GL (Fin n) ℚ)} *
            ((GL_pair n).H : Set _) =
            {(diagMat_delta n c : GL (Fin n) ℚ)} *
              ((GL_pair n).H : Set _)}
  let TgtType : Type := {p : decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a)) ×
            decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b)) |
            ({(p.1.out : GL (Fin n) ℚ) *
              ((HeckeCoset.rep (T_diag a) : (GL_pair n).Δ) : GL (Fin n) ℚ)} : Set _) *
            {(p.2.out : GL (Fin n) ℚ) *
              ((HeckeCoset.rep (T_diag b) : (GL_pair n).Δ) : GL (Fin n) ℚ)} *
            ((GL_pair n).H : Set _) =
            {((HeckeCoset.rep (T_diag c) : (GL_pair n).Δ) : GL (Fin n) ℚ)} *
              ((GL_pair n).H : Set _)}
  let f : SrcType → TgtType := fun ⟨⟨i, j⟩, hcond⟩ ↦
    ⟨(⟦Lc * i.out * La⁻¹⟧,
      ⟦compensatedYbase dA (Lc * i.out * La⁻¹) (Ra⁻¹ * j.out * Lb⁻¹)⟧),
      by
        have h_iff := fiber_diagMat_iff_mem_H a b c ha hb hc i.out j.out
        rw [← h_dval_a, ← h_dval_b, ← h_dval_c] at h_iff
        have h_diag_mem_pre := h_iff.mp hcond
        have h_diag_mem : (diagMat n c)⁻¹ * (i.out : GL (Fin n) ℚ) * diagMat n a *
            (j.out : GL (Fin n) ℚ) * diagMat n b ∈ (GL_pair n).H := by
          convert h_diag_mem_pre using 2 <;> simp [h_dval_a, h_dval_b, h_dval_c]
        have h_rep_mem : (HeckeCoset.rep (T_diag c) : GL (Fin n) ℚ)⁻¹ *
            ((Lc * i.out * La⁻¹ : (GL_pair n).H) : GL (Fin n) ℚ) *
            (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) *
            ((Ra⁻¹ * j.out * Lb⁻¹ : (GL_pair n).H) : GL (Fin n) ℚ) *
            (HeckeCoset.rep (T_diag b) : GL (Fin n) ℚ) ∈ (GL_pair n).H := by
          apply (rep_mem_H_iff_compensated_diag_mem_H a b c La Ra Lb Rb Lc Rc
            hDecA hDecB hDecC (Lc * i.out * La⁻¹) (Ra⁻¹ * j.out * Lb⁻¹)).mpr
          have h_simp_i : (Lc⁻¹ * (Lc * i.out * La⁻¹) * La : (GL_pair n).H) = i.out := by
            group
          have h_simp_j : (Ra * (Ra⁻¹ * j.out * Lb⁻¹) * Lb : (GL_pair n).H) = j.out := by
            group
          rw [h_simp_i, h_simp_j]
          exact h_diag_mem
        have h_iff_lift := fiber_rep_iff_mem_H a b c
          (Lc * i.out * La⁻¹) (Ra⁻¹ * j.out * Lb⁻¹)
        have h_rc_lift := h_iff_lift.mpr h_rep_mem
        exact coset_cond_of_compensated_out dA (HeckeCoset.rep (T_diag b))
          (HeckeCoset.rep (T_diag c)) (Lc * i.out * La⁻¹) (Ra⁻¹ * j.out * Lb⁻¹)
          (by rw [← Set.singleton_mul_singleton]; exact h_rc_lift)⟩
  simp only [HeckeRing.heckeMultiplicity]
  norm_cast
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨⟨i₁, j₁⟩, _⟩ ⟨⟨i₂, j₂⟩, _⟩ heq
  have heq_pair := Subtype.mk.inj heq
  have h_i_eq : (⟦Lc * i₁.out * La⁻¹⟧ :
      decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a))) =
      ⟦Lc * i₂.out * La⁻¹⟧ := (Prod.mk.injEq _ _ _ _).mp heq_pair |>.1
  have h_j_eq : (⟦compensatedYbase dA (Lc * i₁.out * La⁻¹) (Ra⁻¹ * j₁.out * Lb⁻¹)⟧ :
      decompQuot (GL_pair n) (HeckeCoset.rep (T_diag b))) =
      ⟦compensatedYbase dA (Lc * i₂.out * La⁻¹) (Ra⁻¹ * j₂.out * Lb⁻¹)⟧ :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.2
  have h_i_final : i₁ = i₂ := by
    rw [Quotient.eq] at h_i_eq
    change QuotientGroup.leftRel _ (Lc * i₁.out * La⁻¹) (Lc * i₂.out * La⁻¹) at h_i_eq
    refine decompQuot_eq_of_inv_out_mul_mem (g := diagMat_delta n a) ?_
    have h_fwd := decompQuot_asymm_first_wd (n := n) a ha La Ra Lc hDecA
      (Lc * i₁.out * La⁻¹) (Lc * i₂.out * La⁻¹) h_i_eq
    rw [QuotientGroup.leftRel_apply] at h_fwd
    have h_simp : (Lc⁻¹ * (Lc * i₁.out * La⁻¹) * La)⁻¹ *
        (Lc⁻¹ * (Lc * i₂.out * La⁻¹) * La) = i₁.out⁻¹ * i₂.out := by group
    rwa [h_simp] at h_fwd
  subst h_i_final
  have h_j_cancel := decompQuot_left_mul_cancel
    (HeckeCoset.rep (T_diag b))
    ⟨_, conjAct_inv_mem_of_subgroupOf (dA : GL (Fin n) ℚ)
      (outShift dA (Lc * i₁.out * La⁻¹))⟩
    (Ra⁻¹ * j₁.out * Lb⁻¹) (Ra⁻¹ * j₂.out * Lb⁻¹) h_j_eq
  have h_j_final : j₁ = j₂ := by
    rw [Quotient.eq] at h_j_cancel
    change QuotientGroup.leftRel _ (Ra⁻¹ * j₁.out * Lb⁻¹) (Ra⁻¹ * j₂.out * Lb⁻¹)
      at h_j_cancel
    refine decompQuot_eq_of_inv_out_mul_mem (g := diagMat_delta n b) ?_
    have h_fwd := decompQuot_asymm_second_wd (n := n) b hb Lb Rb Ra hDecB
      (Ra⁻¹ * j₁.out * Lb⁻¹) (Ra⁻¹ * j₂.out * Lb⁻¹) h_j_cancel
    rw [QuotientGroup.leftRel_apply] at h_fwd
    have h_simp : (Ra * (Ra⁻¹ * j₁.out * Lb⁻¹) * Lb)⁻¹ *
        (Ra * (Ra⁻¹ * j₂.out * Lb⁻¹) * Lb) = j₁.out⁻¹ * j₂.out := by group
    rwa [h_simp] at h_fwd
  subst h_j_final
  rfl

/-- The Hecke multiplicity at the `rep T_diag` level equals the multiplicity at the
`diagMat_delta` level. -/
lemma heckeMultiplicity_rep_eq_diagMat_delta {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) :
    HeckeRing.heckeMultiplicity (GL_pair n)
        (HeckeCoset.rep (T_diag a)) (HeckeCoset.rep (T_diag b))
        (HeckeCoset.rep (T_diag c)) =
    HeckeRing.heckeMultiplicity (GL_pair n)
        (diagMat_delta n a) (diagMat_delta n b) (diagMat_delta n c) :=
  le_antisymm (heckeMultiplicity_rep_le_diagMat_delta a b c ha hb hc)
    (heckeMultiplicity_diagMat_le_rep_delta a b c ha hb hc)

end HeckeRing.GLn
