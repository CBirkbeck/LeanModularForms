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
results from the layered development under `BlockBijection/`:

* `AbstractHeckePair` — abstract `HeckePair` stabilizer/coset lemmas
* `BlockEmbed` — `slSuccEmbed`/`blockEmbedGL` and dimension reduction
* `HeckeMultBridge` — lattice model and rep ↔ diagMat bridge (`≥` direction)
* `SLReduction` — SL row/column/Bezout/divChain reduction
* `TrailingHNF` — trailing-block HNF / column-HNF construction
* `StabFiberIBlock` — stabilizer and fiber block-form (i-side)
* `FiberPreimageJ` — j-side preimage (`fiber_block_form_preimage`)

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

/-- **Hybrid `≤` direction with mulMap-form target.** Same source predicate as
`heckeMultiplicity_block_embed_le_diagMat` (set-form `heckeMultiplicity` at
dim `k+2`), but the dim-`(k+1)` target count is the rep-invariant
`heckeMultiplicityMulMap` form. Proof: chain the existing `_le_` direction with
the forward bridge `heckeMultiplicity_le_heckeMultiplicityMulMap`.

This is the **forward-compatible API** for downstream consumers that can accept
the target-side count in the mulMap form.  The reverse hybrid direction
(mulMap-form on the source side) is not currently provided: the
`heckeMultiplicity_le_heckeMultiplicityMulMap` bridge is one-way only, so going
mulMap → set-form would require an additional compensation construction that is
not part of this API.

Inherits the `fiber_has_block_form_preimages` sorry from the source `_le_`
direction; no new sorries are introduced here.

**Recommended replacement.**  Downstream consumers that wish a sorry-free
proof of the same statement should use
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_sorryFree`
(declared later in this file).  That public theorem delivers the same
inequality via Route A's direct chain (`_via_iFunctional` (T197) +
explicit corrected-j chain (T199) + `N_of_i_default` (T204)), bypassing
the `fiber_has_block_form_preimages` sorry entirely.  It preserves this
lemma's signature for drop-in substitution. -/
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

/-- **Hybrid `≥` direction with mulMap-form target.** Same source predicate as
`heckeMultiplicity_block_embed_ge_diagMat` (set-form `heckeMultiplicity` at
dim `k+1`), but the dim-`(k+2)` target count is the rep-invariant
`heckeMultiplicityMulMap` form. Proof: chain the existing `_ge_` direction with
the forward bridge `heckeMultiplicity_le_heckeMultiplicityMulMap`.

Sorry-free: the underlying `_ge_` direction is sorry-free (compensated injection
via `coset_shift_fwd_q1`), and the bridge is sorry-free. -/
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

/-- **T001 consumer theorem: target-mulMap reduction of the block-embed
multiplicity goal at the diagMat level.**

Packages both target-mulMap hybrid directions (`_le_target_mulMap` and
`_ge_target_mulMap`) into a single statement: the block-embed `heckeMultiplicity`
at dim `(k+1)` and dim `(k+2)` are mutually bounded by the `heckeMultiplicityMulMap`
counts on the opposite side.  This is the strongest packaged statement currently
available without the converse `heckeMultiplicityMulMap → heckeMultiplicity`
direction; downstream consumers that can target-relax to the mulMap form get this
sandwich for free.

Inherits the existing `fiber_has_block_form_preimages` sorry only via the `_le_`
direction; the `_ge_` direction is sorry-free.

**Recommended replacement.**  Downstream consumers that need the same
sandwich without the sorry inheritance should use
`heckeMultiplicity_block_embed_target_mulMap_sandwich_sorryFree`
(declared later in this file). That theorem packages the same statement
but routes the `≤` direction through Route A's direct chain
(`_via_iFunctional` (T197) + explicit corrected-j chain (T199) +
`N_of_i_default` (T204)), eliminating the `fiber_has_block_form_preimages`
sorry entirely.  It preserves this theorem's full signature for drop-in
substitution.  -/
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

/-- **Left-cancellation of a fixed `H`-element on `decompQuot` classes.**
Multiplying the canonical representatives `x.out`, `y.out` on the left by the
same `n : P.H` and taking quotient classes is injective: if
`⟦n * x.out⟧ = ⟦n * y.out⟧` then `x = y`.  This is the rep-invariant cancellation
underlying the j-side injectivity step of
`_le_diagMat_target_mulMap_via_iFunctional`, where the two corrected-j embeds
share the same conjugator `N_of_i i` once the i-classes agree. -/
private lemma decompQuot_out_left_mul_cancel {G : Type*} [Group G] {P : HeckePair G}
    {g : P.Δ} (n : P.H) {x y : decompQuot P g}
    (h : (⟦n * x.out⟧ : decompQuot P g) = ⟦n * y.out⟧) : x = y := by
  rw [Quotient.eq, QuotientGroup.leftRel_apply] at h
  have h_simp : (n * x.out)⁻¹ * (n * y.out) = x.out⁻¹ * y.out := by group
  rw [h_simp] at h
  exact Quotient.out_equiv_out.mp (QuotientGroup.leftRel_apply.mpr h)

/-- **Route A: ≤_diagMat target-mulMap reduction to an i-functional `N_i` extractor.**

Provides a sorry-free proof of the dim-(k+2) → dim-(k+1) `heckeMultiplicity` ≤
`heckeMultiplicityMulMap` inequality, *parameterized* by an `N_of_i` function
returning the conjugating SL element of the corrected-j descent at every fiber
pair, plus a hypothesis `h_iFunctional` asserting that the corrected-j chain's
output uses this specific `N_of_i i` (rather than a `(j, hfib)`-dependent choice).

**Why this is Route A's smallest sufficient form.**  T187 found that canonical
`Quotient.out` j-side col-divisibility is class-non-invariant, so directly
closing `fiber_has_block_form_preimages` is provably impossible without a
refactor that avoids `Quotient.out` rep choice on the j-side.  The corrected-j
chain (`fiber_block_form_preimage_corrected_j_mulMap`, sorry-free) provides the
rep-invariant `mulMap` data, but its `N_i` output is extracted from a
`(j, hfib)`-dependent existential and may differ across `(j, hfib)` pairs
sharing the same `i`.  The injection from the dim-(k+2) fiber set into the
dim-(k+1) `mulMap` fiber set (via `(i, j) ↦ (i_m, j_m)`) is injective IFF
`N_i` depends only on `i` — exactly what `h_iFunctional` captures.

**Closing `h_iFunctional` (remaining work).**  An i-functional `N_of_i` is
obtained by `Classical.choose` on the i-only existentials
`exists_stab_with_block_form_of_fiber` (i-only body) and
`exists_stab_int_conjugate_diagMat_cons_one` (i-only body given `M_i`).  By
Lean 4's proof irrelevance, both `Classical.choose` calls give i-functional
values.  The remaining work to *land* `h_iFunctional` sorry-free is to
refactor the corrected-j chain (`fiber_int_mat_eq_via_i_block`, `_rearr`,
`_rearr_adj`, `hfib_col_div_b_via_i_block`,
`fiber_block_form_preimage_corrected_j`, and `_mulMap`) to take
`(M_i, σ_i, N_i, h_block_i, h_stab_i, h_int_conj)` as **explicit** inputs
(instead of extracting them via the j-dependent combined existential), so
that the chain's `N_i` matches the i-functional `Classical.choose`-extracted
one. Estimated ~700 LOC parameterization across the chain.

**Use site.**  Combined with the existing
`heckeMultiplicity_block_embed_ge_diagMat_target_mulMap` (sorry-free) and the
forward bridge `heckeMultiplicity_le_heckeMultiplicityMulMap`, this closes the
target-mulMap sandwich at dim `(k+1)` and dim `(k+2)` without going through
the canonical `j.out`-divisibility chain at all. -/
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

/-- **i-only block-witness existence proposition.**

Asserts the existence of an i-side block-reduction triple
`(M, σ_m, N)` satisfying:

* `toSL i.out * M = slSuccEmbed σ_m` (block form);
* `M ∈ stab(D_a)` at the GL level (cons-1 stabilizer);
* `D_a · N = M · D_a` over ℤ (integer-conjugate identity).

The proposition mentions only `(a, ha, i)` — no `b, c, j, hfib` — making
it manifestly i-only.  By Lean 4's proof irrelevance, `Classical.choose`
on this proposition gives values that depend only on `(a, ha, i)`. -/
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

/-- **`IBlockWitnessExists` is provable from any fiber pair `(j, hfib)`.**

Combines `exists_stab_with_block_form_of_fiber` (i-side block) and
`exists_stab_int_conjugate_diagMat_cons_one` (integer conjugate) to
construct the i-only existential witness. -/
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

/-- **Default i-functional `N_of_i` extractor.**

Selects the third component (`N`) of the i-only Classical.choose witness
for `IBlockWitnessExists`, falling back to `1` when the existential fails
(which happens only for `i` outside the image of any fiber, where the
count contributes nothing).

By construction, this is a function of `(a, ha, i)` alone — i-functional
in the sense required by
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional`. -/
private noncomputable def N_of_i_default {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a))) :
    SpecialLinearGroup (Fin (k + 2)) ℤ := by
  classical
  exact if h : IBlockWitnessExists a ha i
  then h.choose_spec.choose_spec.choose
  else 1

/-- **Closed-form `_le_diagMat` target-mulMap inequality (Route A complete,
DIRECT proof — no `fiber_has_block_form_preimages` sorry inheritance).**

Combines `heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional`
(T197) with the explicit corrected-j chain (T199) and the i-only
`Classical.choose` extraction of `N_of_i_default` (this ticket) to close
the dim-(k+2) → dim-(k+1) `heckeMultiplicity` ≤ `heckeMultiplicityMulMap`
inequality without any parameterized hypotheses.

**Why a separate `_direct` lemma.**  The pre-existing
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap` (line 8977) is a
hybrid: it chains `heckeMultiplicity_block_embed_le_diagMat` (which still
contains the architectural-blocker sorry at `fiber_has_block_form_preimages`)
with the rep-invariance bridge `heckeMultiplicity_le_heckeMultiplicityMulMap`,
inheriting the sorry as a result.  This `_direct` variant bypasses the
sorry-bearing `_le_diagMat` step entirely by going through the
explicit-chain route, so it requires no `hk : 1 ≤ k` and no `hdc` (which
were artifacts of the sorry-bearing chain).

**Proof outline.**  Apply `_via_iFunctional` with `N_of_i_default a ha`,
reducing to `h_iFunctional`.  For each fiber pair `(i, j, hfib)`:

1. Establish `IBlockWitnessExists a ha i` from the fiber via
   `iBlockWitnessExists_of_fiber`.
2. By `dif_pos`, `N_of_i_default a ha i` unfolds to
   `h_iF.choose_spec.choose_spec.choose` for any proof `h_iF`.
3. Extract the i-functional `(M, σ, N)` triple plus its i-only conditions
   from `h_iF`.
4. Apply `fiber_block_form_preimage_corrected_j_mulMap_explicit` with
   these specific witnesses.

The key `i`-functionality argument is Lean 4's proof irrelevance: any two
proofs of `IBlockWitnessExists a ha i` are equal as elements of `Prop`,
hence `Classical.choose` gives the same value regardless of how the proof
was constructed (in particular, regardless of which `(j, hfib)` was used). -/
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

/-- **Public sorry-free target-mulMap `≤` direction (Route A).**

Public alias for the closed-form
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_direct` that
preserves the original sorry-inheriting hybrid's
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap` signature
(`hk`, `hdc` retained as no-op parameters for signature compatibility).
Downstream consumers that wish to use the sorry-free Route A proof
without touching the canonical `fiber_has_block_form_preimages` blocker
should call this theorem (or its no-`hk`/`hdc` analog
`_le_diagMat_target_mulMap_direct`) instead of the original hybrid.

The two `_` parameters (`_hk`, `_hdc`) are intentionally unused: the
direct Route A proof — built on `_via_iFunctional` (T197), the
explicit corrected-j chain (T199), and the i-functional `N_of_i_default`
extractor (T204) — does not require either `hk : 1 ≤ k` (the
`fiber_block_form_preimage` k=0 exclusion was an artifact of the
canonical-rep chain, not of Route A) or `hdc` (the `c` divisor chain
was used only for the canonical `_le_diagMat`'s sorry'd preimage step). -/
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

/-- **Public sorry-free target-mulMap sandwich theorem (Route A).**

Public sorry-free analog of `heckeMultiplicity_block_embed_target_mulMap_sandwich`
combining `_le_diagMat_target_mulMap_sorryFree` (this ticket) with the
existing sorry-free `_ge_diagMat_target_mulMap`.  Carries the original
sandwich's full signature for compatibility but routes the `≤` direction
through Route A's direct chain, **eliminating the
`fiber_has_block_form_preimages` sorry inheritance** that the original
sandwich theorem still carried via the canonical `_le_diagMat` route.

This is the recommended public API for downstream consumers that need
the dim-(k+1)/dim-(k+2) target-mulMap sandwich at the diagMat level
without entanglement to the architectural-blocker canonical j-side
divisibility chain (T187/T191/T195). -/
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

/-- **Determinant of the trailing `(k+1)×(k+1)` block equals the full determinant
when the first row is `e₀`.**  Cofactor expansion along row `0`: all but the
`(0,0)` term vanish (`hrow0`), and the surviving `(0,0)`-minor is exactly the
trailing block.  Used to transport `det (Y * M) = 1` to `det τ_raw = 1`. -/
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

/-- **A matrix with `e₀` first column and first row, and trailing block `τ`,
equals `slSuccEmbed τ`.**  Checked entrywise on the four `Fin.cases` corner
regions against the `slSuccEmbed_val_*` characterizations. -/
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

/-- **`b`-stabilizer membership is closed under products.**  Conjugation by
`diagMat (k+2) (Fin.cons 1 b)` distributes over the product `P * Q` (via
`map_mul` + `group`), so membership of each factor's conjugate gives membership
of the product's conjugate. -/
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

/-- **`Y · M₀` has first column `e₀` when `M₀`'s first column equals `Y⁻¹`'s.**
Expanding the matrix product on column `0` and substituting `M₀ p 0 = (Y⁻¹) p 0`
collapses the column to `(Y · Y⁻¹) · 0 = 1 · 0 = e₀`.  This is the first-column
clearance step feeding the trailing-block construction. -/
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

/-- **Generic block-form witness from column-zero divisibility.**

Given any `Y ∈ SL(k+2, ℤ)` together with a `DivChain b` and the column-zero
divisibility `b r ∣ (Y⁻¹).val r.succ 0` (the "j-side col-divisibility"
hypothesis), produces `M ∈ SL(k+2, ℤ)` and `τ ∈ SL(k+1, ℤ)` such that:

* `Y * M = slSuccEmbed τ` (block form: first row/column of `Y · M` are
  `e_0` / `e_0^T`; bottom-right block is `τ`);
* `(diagMat (k+2) (Fin.cons 1 b))⁻¹ · mapGL ℚ M · diagMat (k+2) (Fin.cons 1 b)
  ∈ (GL_pair (k+2)).H` (`b`-stabilizer condition).

Mirrors the i-side construction `exists_stab_with_block_form_of_fiber` but
parameterized by an arbitrary `Y` and an arbitrary col-divisibility hypothesis,
making the generic block-reduction step independent of the fiber context.  Uses
`sl_first_col_primitive` (always-applicable primitivity from `Y⁻¹ ∈ SL`) and
`sl_exists_col_stab_divChain` (already proved) for the first column reduction;
then `sl_first_row_clear_with_col0_e0` for the first row clearance.

This is the natural reusable form: applying with `Y := toSL i.out` and
`hfib_col_div_a` recovers `exists_stab_with_block_form_of_fiber`'s i-side
output; applying with `Y := toSL j.out` and a hypothetical `hfib_col_div_b`
delivers the missing j-side block-form witness. -/
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

/-- **j-side block-form witness, conditional on `hfib_col_div_b`.**

Specializes the generic block-form helper `exists_stab_block_form_of_col_div`
to `Y := toSL j.out`, packaging the missing j-side col-divisibility input
`b r ∣ ((toSL j.out)⁻¹).val r.succ 0` as an explicit hypothesis.

This is the **conditional** form of the j-side block witness referred to in
the architectural-blocker docblock below: with the col-divisibility supplied,
the rest of the construction (Bezout column reduction + first-row clearance +
stabilizer closure) goes through generically.

The remaining open question is whether `b r ∣ ((toSL j.out)⁻¹).val r.succ 0`
can be **proved** from the integer matrix equation
`A_i · D_a · A_j · D_b = D_c · ν` (`hfib_int_mat_eq`).  See the docblock below
for the structural asymmetry obstruction; see `hfib_col_div_b_canonical_stmt`
for the smallest precise missing arithmetic statement. -/
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

/-- **Smallest precise missing arithmetic input for the j-side block witness.**

Statement of the col-zero divisibility on `(toSL j.out)⁻¹` that, together with
the existing i-side col-divisibility `hfib_col_div_a`, would supply the j-side
block-form witness `exists_stab_with_block_form_of_fiber_j_side_of_col_div`
unconditionally.

**Open status.**  This statement is the smallest precise mathematical
question whose resolution would mechanically discharge the j-side block
witness.  It is currently UNRESOLVED: the standard adjugate technique used to
prove `hfib_col_div_a` (premultiply by `adjugate A_i` and postmultiply by
`adjugate ν`) does NOT yield the analog for `(toSL j.out)⁻¹`.  Specifically,
the adjugate of the rearranged equation
`A_i · D_a · A_j · D_b = D_c · ν` gives
`adj D_b · adj A_j · adj D_a · adj A_i = adj ν · adj D_c`, and applying mulVec
on `e_0` produces an integer identity of the form
`γ · (adj A_j) r.succ 0 = b_r · Z_r` (where `Z_r ∈ ℤ` and `γ = ∏ c_q`).
This says `b_r ∣ γ · (adj A_j) r.succ 0`, but does **not** strip `γ` to
yield `b_r ∣ (adj A_j) r.succ 0` — `gcd(γ, b_r)` is not generally `1`, so the
divisibility may be entirely absorbed by the `γ` factor.

**Resolution paths beyond `T001`'s adjugate-only toolchain:**
1. A coordinated Smith-normal-form argument tracking `D_a · A_j · D_b`'s
   invariant factors against `D_c · ν` simultaneously, producing a
   "two-sided" block reduction of `A_j` against `D_b` (rather than only
   the "one-sided" reduction of `A_i` against `D_a`).
2. A lattice-theoretic descent isolating the column space of `A_j` modulo
   the `b`-summand of the dim-`(k+2)` lattice, exploiting the `Fin.cons 1`
   constraint on the leading entry of `D_b`.

Both routes require infrastructure beyond `BlockBijection.lean`'s current
scope (e.g. either `Mathlib.LinearAlgebra.Matrix.SmithNormalForm` over `ℤ`
specialized to non-PID-flat divisor chains, or a custom lattice descent
formalization).  -/
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

/-! ### Architectural blocker: missing j-side block-form witness from fiber

The `_le_diagMat` direction's underlying sorry (`fiber_has_block_form_preimages`)
goes through canonical `Quotient.out` representatives, and the rep-control bridge
from existential reps to canonical reps is rep-dependent (refuted by the dim-2
counterexample `a = (1, 4), c = (1, 8), t = [[1, 0], [4, 1]]` documented at
`fiber_has_block_form_preimages_existential_reps`).  An alternative sorry-free
proof path through `fiber_has_block_form_preimages_existential_reps` requires
**both** an i-side block-form witness (provided by
`exists_stab_with_block_form_of_fiber`) and a j-side analog.  The j-side analog
is currently missing; its precise required statement is:

```
private lemma exists_stab_with_block_form_of_fiber_j_side {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (M_j : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (τ_m : SpecialLinearGroup (Fin (k + 1)) ℤ),
      toSL j.out * M_j = slSuccEmbed τ_m ∧
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H
```

**Why current APIs do not supply this.**  The i-side proof
(`exists_stab_with_block_form_of_fiber`) extracts column-zero divisibility
`a r ∣ (toSL i.out)⁻¹ r.succ 0` from the integer matrix equation
`A_i · D_a · A_j · D_b = D_c · ν` (`hfib_int_mat_eq`) by premultiplying by
`adjugate A_i` and postmultiplying by `adjugate ν`, which cancels `A_i` and `ν`
and isolates the desired column.  The same argument template applied to extract
`b r ∣ (toSL j.out)⁻¹ r.succ 0` runs into structural asymmetry:

* Transposing the equation to `D_b · A_j^T · D_a · A_i^T = ν^T · D_c` produces
  the form `D · A · D · A`, not the `A · D · A · D = D · M` form that the
  template requires (the leading factor on the LHS is now a diagonal `D_b`,
  whose adjugate is also diagonal and does not cancel cleanly into a row-extraction
  identity).
* Inverting the equation to isolate `A_j⁻¹` produces `A_j⁻¹ = D_b · ν⁻¹ · D_c⁻¹ · A_i · D_a`
  over `ℚ`; the `D_c⁻¹` factor is non-integer in general, so the resulting
  expression for column 0 of `A_j⁻¹` is `b'_r · (rational expression)`, which
  forces integer-divisibility of `(A_j⁻¹) r.succ 0` by `b r` only modulo
  divisibility constraints that are not immediate from `hfib`.

The structural asymmetry is intrinsic: `i.out` appears at the leftmost position
of the product `i.out · D_a · j.out · D_b`, with `D_a` immediately on its right;
`j.out` appears in the interior, with both `D_a` and `D_b` adjacent.  Extracting
"first-column divisibility of the inverse" from each factor therefore requires
asymmetric algebraic manipulations.

**Resolution paths (out of T001 prototype scope):**
1. A coordinated Smith-normal-form construction simultaneously block-reducing
   both `i.out` and `j.out` against `D_a, D_b, D_c, ν`, exploiting the cons-1
   constraint on the leading diagonal entries.
2. A lattice-theoretic argument projecting the dim-`(k+2)` fiber pair onto a
   dim-`(k+1)` sublattice via the ℤu_0-summand decomposition, recovering both
   block witnesses from a single lattice-level descent.

Either route yields the j-side block witness, which combined with the existing
i-side witness feeds `fiber_has_block_form_preimages_existential_reps` and
discharges the residual sorry. -/

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
