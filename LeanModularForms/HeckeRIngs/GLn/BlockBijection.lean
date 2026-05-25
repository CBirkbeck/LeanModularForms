/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.BlockBijection.FiberPreimageJ

/-!
# Block Embedding Bijection for Hecke Multiplicities

Shimura's Lemma 3.19: the Hecke multiplicity at block-embedded cosets in
dimension `m+1` equals the multiplicity in dimension `m`.

This top module assembles the `≤`/`≥`/sandwich `heckeMultiplicity_block_embed`
results from the layered development under `BlockBijection/`.

## References

* Shimura, §3.2, Lemma 3.19, Proposition 3.15
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset
open Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable {m : ℕ} [NeZero m]

/-- **Diagonal-level ≤ direction of `heckeMultiplicity_block_embed`.** Injection
`Fiber_{k+2}^{cons1} → Fiber_{k+1}` built from `fiber_block_form_preimage` and
`decompQuot_slSuccEmbed_diagMat_injective`. Inherits the `hk : 1 ≤ k` restriction
from `fiber_block_form_preimage`. -/
lemma heckeMultiplicity_block_embed_le_diagMat {k : ℕ} (hk : 1 ≤ k)
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) (hdc : DivChain (k + 1) c) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
    HeckeRing.heckeMultiplicity (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) := by
  let SrcType : Type := {p : decompQuot (GL_pair (k + 2))
            (diagMat_delta (k + 2) (Fin.cons 1 a)) ×
            decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)) |
            ({(p.1.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
            {(p.2.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
            ((GL_pair (k + 2)).H : Set _) =
            {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
              ((GL_pair (k + 2)).H : Set _)}
  let TgtType : Type := {p : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a) ×
            decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b) |
            ({(p.1.out : GL (Fin (k + 1)) ℚ) *
              (diagMat_delta (k + 1) a : GL (Fin (k + 1)) ℚ)} : Set _) *
            {(p.2.out : GL (Fin (k + 1)) ℚ) *
              (diagMat_delta (k + 1) b : GL (Fin (k + 1)) ℚ)} *
            ((GL_pair (k + 1)).H : Set _) =
            {(diagMat_delta (k + 1) c : GL (Fin (k + 1)) ℚ)} *
              ((GL_pair (k + 1)).H : Set _)}
  let f : SrcType → TgtType := fun ⟨⟨i, j⟩, hfib⟩ ↦
    let spec := fiber_block_form_preimage hk a b c ha hb hc hda hdb hdc i j hfib
    let i_m := spec.choose
    let spec' := spec.choose_spec
    let j_m := spec'.choose
    ⟨(i_m, j_m), spec'.choose_spec.2.2⟩
  simp only [HeckeRing.heckeMultiplicity]
  norm_cast
  refine Nat.card_le_card_of_injective f ?_
  rintro ⟨⟨i₁, j₁⟩, hfib₁⟩ ⟨⟨i₂, j₂⟩, hfib₂⟩ heq
  set spec₁ := fiber_block_form_preimage hk a b c ha hb hc hda hdb hdc i₁ j₁ hfib₁ with hspec₁
  set spec₂ := fiber_block_form_preimage hk a b c ha hb hc hda hdb hdc i₂ j₂ hfib₂ with hspec₂
  have heq_pair := Subtype.mk.inj heq
  have h_i_eq : spec₁.choose = spec₂.choose :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.1
  have h_j_eq : spec₁.choose_spec.choose = spec₂.choose_spec.choose :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.2
  have h_spec_i₁ : decompQuot_slSuccEmbed_diagMat a ha spec₁.choose = i₁ :=
    spec₁.choose_spec.choose_spec.1
  have h_spec_j₁ : decompQuot_slSuccEmbed_diagMat b hb spec₁.choose_spec.choose = j₁ :=
    spec₁.choose_spec.choose_spec.2.1
  have h_spec_i₂ : decompQuot_slSuccEmbed_diagMat a ha spec₂.choose = i₂ :=
    spec₂.choose_spec.choose_spec.1
  have h_spec_j₂ : decompQuot_slSuccEmbed_diagMat b hb spec₂.choose_spec.choose = j₂ :=
    spec₂.choose_spec.choose_spec.2.1
  have h_i_final : i₁ = i₂ := by
    rw [← h_spec_i₁, ← h_spec_i₂, h_i_eq]
  have h_j_final : j₁ = j₂ := by
    rw [← h_spec_j₁, ← h_spec_j₂, h_j_eq]
  exact Subtype.ext (Prod.ext h_i_final h_j_final)

/-- Hybrid `≤` direction with mulMap-form target: same source predicate as
`heckeMultiplicity_block_embed_le_diagMat`, but the dim-`(k+1)` target count is
the rep-invariant `heckeMultiplicityMulMap` form. For a proof not depending on
the `fiber_has_block_form_preimages` blocker, use
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_sorryFree`. -/
lemma heckeMultiplicity_block_embed_le_diagMat_target_mulMap {k : ℕ} (hk : 1 ≤ k)
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) (hdc : DivChain (k + 1) c) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
    HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) :=
  le_trans
    (heckeMultiplicity_block_embed_le_diagMat hk a b c ha hb hc hda hdb hdc)
    (HeckeRing.heckeMultiplicity_le_heckeMultiplicityMulMap (GL_pair (k + 1))
      (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c))

/-- Hybrid `≥` direction with mulMap-form target: same source predicate as
`heckeMultiplicity_block_embed_ge_diagMat`, but the dim-`(k+2)` target count is
the rep-invariant `heckeMultiplicityMulMap` form. -/
lemma heckeMultiplicity_block_embed_ge_diagMat_target_mulMap {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ≤
    HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) :=
  le_trans
    (heckeMultiplicity_block_embed_ge_diagMat a b c ha hb hc)
    (HeckeRing.heckeMultiplicity_le_heckeMultiplicityMulMap (GL_pair (k + 2))
      (diagMat_delta (k + 2) (Fin.cons 1 a))
      (diagMat_delta (k + 2) (Fin.cons 1 b))
      (diagMat_delta (k + 2) (Fin.cons 1 c)))

/-- Target-mulMap reduction of the block-embed multiplicity goal at the diagMat
level: the block-embed `heckeMultiplicity` at dim `(k+1)` and dim `(k+2)` are
mutually bounded by the `heckeMultiplicityMulMap` counts on the opposite side.
For a version not depending on the `fiber_has_block_form_preimages` blocker, use
`heckeMultiplicity_block_embed_target_mulMap_sandwich_sorryFree`. -/
theorem heckeMultiplicity_block_embed_target_mulMap_sandwich {k : ℕ} (hk : 1 ≤ k)
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) (hdc : DivChain (k + 1) c) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
      HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ∧
    HeckeRing.heckeMultiplicity (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ≤
      HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) :=
  ⟨heckeMultiplicity_block_embed_le_diagMat_target_mulMap hk a b c ha hb hc hda hdb hdc,
   heckeMultiplicity_block_embed_ge_diagMat_target_mulMap a b c ha hb hc⟩

private lemma decompQuot_out_left_mul_cancel {G : Type*} [Group G] {P : HeckePair G}
    {g : P.Δ} (n : P.H) {x y : decompQuot P g}
    (h : (⟦n * x.out⟧ : decompQuot P g) = ⟦n * y.out⟧) : x = y := by
  rw [Quotient.eq, QuotientGroup.leftRel_apply] at h
  have h_simp : (n * x.out)⁻¹ * (n * y.out) = x.out⁻¹ * y.out := by group
  rw [h_simp] at h
  exact Quotient.out_equiv_out.mp (QuotientGroup.leftRel_apply.mpr h)

/-- The dim-`(k+2)` → dim-`(k+1)` `heckeMultiplicity` ≤ `heckeMultiplicityMulMap`
inequality, parameterized by an `N_of_i` function returning the conjugating SL
element of the corrected-j descent, plus a hypothesis `h_iFunctional` asserting
that the descent output depends only on `i`. The injection on fiber sets is
injective precisely because `N_of_i i` is `i`-functional. -/
lemma heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional
    {k : ℕ} (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (N_of_i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)) →
              SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_iFunctional :
      ∀ (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
        (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
        (_hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
            (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
            {(j.out : GL (Fin (k + 2)) ℚ) *
              (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
            ((GL_pair (k + 2)).H : Set _) =
            {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
              ((GL_pair (k + 2)).H : Set _)),
        ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
          (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
          decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
          decompQuot_slSuccEmbed_diagMat b hb j_m =
            (⟦(⟨mapGL ℚ (N_of_i i)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i)⁻¹⟩ :
                (GL_pair (k + 2)).H) * j.out⟧ :
              decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
          HeckeRing.mulMap (GL_pair (k + 1))
              (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨i_m, j_m⟩ =
            (⟦diagMat_delta (k + 1) c⟧ :
              HeckeRing.HeckeCoset (GL_pair (k + 1)))) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
    HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b)
        (diagMat_delta (k + 1) c) := by
  let _ := hda; let _ := hdb; let _ := hc
  simp only [HeckeRing.heckeMultiplicity, HeckeRing.heckeMultiplicityMulMap]
  norm_cast
  refine Nat.card_le_card_of_injective
    (fun ⟨⟨i, j⟩, hfib⟩ ↦
      ⟨((h_iFunctional i j hfib).choose, (h_iFunctional i j hfib).choose_spec.choose),
        (h_iFunctional i j hfib).choose_spec.choose_spec.2.2⟩) ?_
  rintro ⟨⟨i₁, j₁⟩, hfib₁⟩ ⟨⟨i₂, j₂⟩, hfib₂⟩ heq
  set spec₁ := h_iFunctional i₁ j₁ hfib₁ with hspec₁
  set spec₂ := h_iFunctional i₂ j₂ hfib₂ with hspec₂
  have heq_pair := Subtype.mk.inj heq
  have h_i_m_eq : spec₁.choose = spec₂.choose :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.1
  have h_j_m_eq : spec₁.choose_spec.choose = spec₂.choose_spec.choose :=
    (Prod.mk.injEq _ _ _ _).mp heq_pair |>.2
  have h_i_canon₁ : decompQuot_slSuccEmbed_diagMat a ha spec₁.choose = i₁ :=
    spec₁.choose_spec.choose_spec.1
  have h_j_corr₁ :
      decompQuot_slSuccEmbed_diagMat b hb spec₁.choose_spec.choose =
        (⟦(⟨mapGL ℚ (N_of_i i₁)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i₁)⁻¹⟩ :
            (GL_pair (k + 2)).H) * j₁.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) :=
    spec₁.choose_spec.choose_spec.2.1
  have h_i_canon₂ : decompQuot_slSuccEmbed_diagMat a ha spec₂.choose = i₂ :=
    spec₂.choose_spec.choose_spec.1
  have h_j_corr₂ :
      decompQuot_slSuccEmbed_diagMat b hb spec₂.choose_spec.choose =
        (⟦(⟨mapGL ℚ (N_of_i i₂)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i₂)⁻¹⟩ :
            (GL_pair (k + 2)).H) * j₂.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) :=
    spec₂.choose_spec.choose_spec.2.1
  have h_i_final : i₁ = i₂ := by
    rw [← h_i_canon₁, ← h_i_canon₂, h_i_m_eq]
  have h_j_final : j₁ = j₂ := by
    have h_class_eq :
        (⟦(⟨mapGL ℚ (N_of_i i₁)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i₁)⁻¹⟩ :
            (GL_pair (k + 2)).H) * j₁.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) =
        ⟦(⟨mapGL ℚ (N_of_i i₂)⁻¹, coe_mem_SLnZ (k + 2) (N_of_i i₂)⁻¹⟩ :
            (GL_pair (k + 2)).H) * j₂.out⟧ := by
      rw [← h_j_corr₁, ← h_j_corr₂, h_j_m_eq]
    rw [h_i_final] at h_class_eq
    exact decompQuot_out_left_mul_cancel _ h_class_eq
  exact Subtype.ext (Prod.ext h_i_final h_j_final)

private def IBlockWitnessExists {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a))) :
    Prop :=
  ∃ (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_m : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ),
    toSL i.out * M = slSuccEmbed σ_m ∧
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
    Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N.val =
      M.val *
      Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))

private lemma iBlockWitnessExists_of_fiber {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    IBlockWitnessExists a ha i := by
  obtain ⟨M, σ_m, h_block, h_stab⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M h_stab
  exact ⟨M, σ_m, N, h_block, h_stab, h_int_conj⟩

private noncomputable def N_of_i_default {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a))) :
    SpecialLinearGroup (Fin (k + 2)) ℤ := by
  classical
  exact if h : IBlockWitnessExists a ha i
  then h.choose_spec.choose_spec.choose
  else 1

private lemma heckeMultiplicity_block_embed_le_diagMat_target_mulMap_direct
    {k : ℕ} (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
    HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b)
        (diagMat_delta (k + 1) c) := by
  refine heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional
    a b c ha hb hc hda hdb (N_of_i_default a ha) ?_
  intro i j hfib
  have h_iF : IBlockWitnessExists a ha i :=
    iBlockWitnessExists_of_fiber a b c ha hb hc hda i j hfib
  have h_N_def :
      N_of_i_default a ha i = h_iF.choose_spec.choose_spec.choose := by
    classical
    show (if h : IBlockWitnessExists a ha i
          then h.choose_spec.choose_spec.choose else 1) = _
    rw [dif_pos h_iF]
  set M_i : SpecialLinearGroup (Fin (k + 2)) ℤ := h_iF.choose with hM_i_def
  set σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ :=
    h_iF.choose_spec.choose with hσ_i_def
  set N_i : SpecialLinearGroup (Fin (k + 2)) ℤ :=
    h_iF.choose_spec.choose_spec.choose with hN_i_def
  have h_block_i : toSL i.out * M_i = slSuccEmbed σ_i :=
    h_iF.choose_spec.choose_spec.choose_spec.1
  have h_stab_i : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H :=
    h_iF.choose_spec.choose_spec.choose_spec.2.1
  have h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) :=
    h_iF.choose_spec.choose_spec.choose_spec.2.2
  have h_N_eq : N_of_i_default a ha i = N_i := h_N_def.trans hN_i_def.symm
  rw [h_N_eq]
  exact fiber_block_form_preimage_corrected_j_mulMap_explicit a b c ha hb hc
    hdb i M_i σ_i h_block_i h_stab_i N_i h_int_conj j hfib

/-- Target-mulMap `≤` direction without dependence on the
`fiber_has_block_form_preimages` blocker. Same statement as the hybrid
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap`; the `_hk` and `_hdc`
parameters are retained for signature compatibility but are unused by the
underlying proof. -/
lemma heckeMultiplicity_block_embed_le_diagMat_target_mulMap_sorryFree
    {k : ℕ} (_hk : 1 ≤ k) (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (_hdc : DivChain (k + 1) c) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
    HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b)
        (diagMat_delta (k + 1) c) :=
  heckeMultiplicity_block_embed_le_diagMat_target_mulMap_direct
    a b c ha hb hc hda hdb

/-- Target-mulMap sandwich at the diagMat level without dependence on the
`fiber_has_block_form_preimages` blocker: same statement as
`heckeMultiplicity_block_embed_target_mulMap_sandwich`, routing the `≤` direction
through `heckeMultiplicity_block_embed_le_diagMat_target_mulMap_sorryFree`. -/
theorem heckeMultiplicity_block_embed_target_mulMap_sandwich_sorryFree
    {k : ℕ} (hk : 1 ≤ k) (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (hdc : DivChain (k + 1) c) :
    HeckeRing.heckeMultiplicity (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) ≤
      HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ∧
    HeckeRing.heckeMultiplicity (GL_pair (k + 1))
        (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) (diagMat_delta (k + 1) c) ≤
      HeckeRing.heckeMultiplicityMulMap (GL_pair (k + 2))
        (diagMat_delta (k + 2) (Fin.cons 1 a))
        (diagMat_delta (k + 2) (Fin.cons 1 b))
        (diagMat_delta (k + 2) (Fin.cons 1 c)) :=
  ⟨heckeMultiplicity_block_embed_le_diagMat_target_mulMap_sorryFree hk a b c ha hb hc
      hda hdb hdc,
   heckeMultiplicity_block_embed_ge_diagMat_target_mulMap a b c ha hb hc⟩

private lemma trailing_block_det_of_first_row_e0 {k : ℕ} {R : Type*} [CommRing R]
    (N : Matrix (Fin (k + 2)) (Fin (k + 2)) R)
    (h00 : N 0 0 = 1) (hrow0 : ∀ l : Fin (k + 1), N 0 l.succ = 0) :
    (Matrix.of fun I J : Fin (k + 1) ↦ N I.succ J.succ).det = N.det := by
  symm
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have h_zero_terms : ∀ j : Fin (k + 1),
      (-1 : R) ^ (j.succ : ℕ) * N 0 j.succ *
        (N.submatrix Fin.succ j.succ.succAbove).det = 0 := by
    intro j; rw [hrow0 j]; ring
  rw [Finset.sum_eq_zero (fun j _ ↦ h_zero_terms j), add_zero, h00]
  simp only [Fin.val_zero, pow_zero, one_mul, mul_one]
  have h_submat :
      N.submatrix Fin.succ (0 : Fin (k + 2)).succAbove =
        Matrix.of fun I J : Fin (k + 1) ↦ N I.succ J.succ := by
    ext I J
    show N I.succ ((0 : Fin (k + 2)).succAbove J) = N I.succ J.succ
    rw [Fin.succAbove_zero]
  rw [h_submat]

private lemma eq_slSuccEmbed_of_border_e0 {k : ℕ}
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ) (τ : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h00 : N.val 0 0 = 1) (hrow0 : ∀ l : Fin (k + 1), N.val 0 l.succ = 0)
    (hcol0 : ∀ I : Fin (k + 1), N.val I.succ 0 = 0)
    (hblock : ∀ I J : Fin (k + 1), N.val I.succ J.succ = τ.val I J) :
    N = slSuccEmbed τ := by
  apply Subtype.ext
  ext I J
  refine Fin.cases ?_ ?_ I
  · refine Fin.cases ?_ ?_ J
    · rw [h00, slSuccEmbed_val_zero_zero]
    · intro J'; rw [hrow0 J', slSuccEmbed_val_zero_succ]
  · intro I'
    refine Fin.cases ?_ ?_ J
    · rw [hcol0 I', slSuccEmbed_val_succ_zero]
    · intro J'; rw [hblock I' J', slSuccEmbed_val_succ_succ]

private lemma diagMat_conj_mem_H_mul {k : ℕ} (b : Fin (k + 1) → ℕ)
    (P Q : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hP : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ P : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H)
    (hQ : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ Q : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H) :
    (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ (P * Q) : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  have h_split : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ (P * Q) : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) =
      ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ P : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b)) *
      ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ Q : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b)) := by
    rw [map_mul]; group
  rw [h_split]
  exact mul_mem hP hQ

private lemma mul_first_col_eq_one_of_col_eq_inv_col {k : ℕ}
    (Y M_0 : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_col : ∀ p, M_0.val p 0 = (Y⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).val p 0) :
    ∀ r : Fin (k + 2),
      (Y * M_0).val r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
  intro r
  have h_to_inv :
      (Y * M_0).val r 0 = (Y * Y⁻¹ : SpecialLinearGroup _ ℤ).val r 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun p _ ↦ by rw [h_col p])
  rw [h_to_inv, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

private lemma exists_stab_block_form_of_col_div {k : ℕ}
    (b : Fin (k + 1) → ℕ) (hb : ∀ i, 0 < b i) (hdb : DivChain (k + 1) b)
    (Y : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_col_div_b : ∀ r : Fin (k + 1),
      (b r : ℤ) ∣
        (Y⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).val r.succ 0) :
    ∃ (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (τ : SpecialLinearGroup (Fin (k + 1)) ℤ),
      Y * M = slSuccEmbed τ ∧
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  have hw_primitive :
      ∀ d : ℤ, (∀ r : Fin (k + 2),
          d ∣ (Y⁻¹ : SpecialLinearGroup _ ℤ).val r 0) → IsUnit d :=
    fun d hd ↦ sl_first_col_primitive (Y⁻¹) d hd
  obtain ⟨M_0, hM_0_col, hM_0_stab⟩ :=
    sl_exists_col_stab_divChain b hb hdb
      (fun r ↦ (Y⁻¹ : SpecialLinearGroup _ ℤ).val r 0)
      hw_primitive h_col_div_b
  have h_col_e0 : ∀ r : Fin (k + 2),
      (Y * M_0).val r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 :=
    mul_first_col_eq_one_of_col_eq_inv_col Y M_0 hM_0_col
  obtain ⟨T_clear, hT_col0, hT_S, _, _, hT_stab⟩ :=
    sl_first_row_clear_with_col0_e0 b hb (Y * M_0) h_col_e0 Finset.univ
  set M : SpecialLinearGroup (Fin (k + 2)) ℤ := M_0 * T_clear with hM_def
  set N_full : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (Y * M).val with hN_def
  have hM_assoc : Y * M = (Y * M_0) * T_clear := by
    rw [hM_def]; exact (mul_assoc _ _ _).symm
  have hN_col0 : ∀ r : Fin (k + 2),
      N_full r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    show (Y * M).val r 0 = _
    rw [hM_assoc, hT_col0 r]
    exact h_col_e0 r
  have hN_row0 : ∀ l : Fin (k + 1), N_full 0 l.succ = 0 := by
    intro l
    show (Y * M).val 0 l.succ = _
    rw [hM_assoc]
    exact hT_S l (Finset.mem_univ l)
  have hN_00 : N_full 0 0 = 1 := by simpa using hN_col0 0
  have hN_succ0 : ∀ I : Fin (k + 1), N_full I.succ 0 = 0 := fun I ↦ by
    simpa [Matrix.one_apply_ne (Fin.succ_ne_zero I)] using hN_col0 I.succ
  set τ_raw : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun I J ↦ N_full I.succ J.succ with hτ_raw_def
  have h_det : τ_raw.det = 1 :=
    (trailing_block_det_of_first_row_e0 N_full hN_00 hN_row0).trans
      (hN_def ▸ (Y * M).2)
  set τ : SpecialLinearGroup (Fin (k + 1)) ℤ := ⟨τ_raw, h_det⟩ with hτ_def
  have h_block : Y * M = slSuccEmbed τ :=
    eq_slSuccEmbed_of_border_e0 (Y * M) τ hN_00 hN_row0 hN_succ0 (fun _ _ ↦ rfl)
  have h_M_stab : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
    rw [hM_def]
    exact diagMat_conj_mem_H_mul b M_0 T_clear hM_0_stab hT_stab
  exact ⟨M, τ, h_block, h_M_stab⟩

private lemma exists_stab_with_block_form_of_fiber_j_side_of_col_div {k : ℕ}
    (b : Fin (k + 1) → ℕ) (hb : ∀ i, 0 < b i) (hdb : DivChain (k + 1) b)
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (h_col_div_b : ∀ r : Fin (k + 1),
      (b r : ℤ) ∣
        ((toSL j.out)⁻¹ :
          SpecialLinearGroup (Fin (k + 2)) ℤ).val r.succ 0) :
    ∃ (M_j : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (τ_m : SpecialLinearGroup (Fin (k + 1)) ℤ),
      toSL j.out * M_j = slSuccEmbed τ_m ∧
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H :=
  exists_stab_block_form_of_col_div b hb hdb (toSL j.out) h_col_div_b

/-- The col-zero divisibility on `(toSL j.out)⁻¹` that, together with the i-side
col-divisibility, would supply the j-side block-form witness
`exists_stab_with_block_form_of_fiber_j_side_of_col_div` unconditionally. -/
def hfib_col_div_b_canonical_stmt : Prop :=
  ∀ {k : ℕ} (a b c : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hb : ∀ i, 0 < b i)
    (_hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (_hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)),
    ∀ r : Fin (k + 1),
      (b r : ℤ) ∣
        ((toSL j.out)⁻¹ :
          SpecialLinearGroup (Fin (k + 2)) ℤ).val r.succ 0

lemma heckeMultiplicity_block_embed [NeZero (m + 1)]
    (a b c : Fin m → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain m a) (hdb : DivChain m b) (hdc : DivChain m c) (hm : 2 ≤ m) :
    HeckeRing.heckeMultiplicity (GL_pair (m + 1))
      (HeckeCoset.rep (T_diag (Fin.cons 1 a)))
      (HeckeCoset.rep (T_diag (Fin.cons 1 b)))
      (HeckeCoset.rep (T_diag (Fin.cons 1 c))) =
    HeckeRing.heckeMultiplicity (GL_pair m)
      (HeckeCoset.rep (T_diag a))
      (HeckeCoset.rep (T_diag b))
      (HeckeCoset.rep (T_diag c)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  have hcons_a := cons_one_pos ha
  have hcons_b := cons_one_pos hb
  have hcons_c := cons_one_pos hc
  have bridge_m := heckeMultiplicity_rep_eq_diagMat_delta (n := k + 1) a b c ha hb hc
  have bridge_m1 := heckeMultiplicity_rep_eq_diagMat_delta (n := k + 2)
    (Fin.cons 1 a) (Fin.cons 1 b) (Fin.cons 1 c) hcons_a hcons_b hcons_c
  rw [bridge_m1, bridge_m]
  exact le_antisymm
    (heckeMultiplicity_block_embed_le_diagMat (k := k) hk a b c ha hb hc hda hdb hdc)
    (heckeMultiplicity_block_embed_ge_diagMat (k := k) a b c ha hb hc)

end HeckeRing.GLn
