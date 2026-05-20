/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.NumberTheory.ModularForms.NormTrace
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed

/-!
# Trace / descent operator from `Γ₁(M)` to `Γ₁(N)` (POST-4h / T120)

Packages Mathlib's `ModularForm.trace` + `CuspForm.trace` (from
`Mathlib.NumberTheory.ModularForms.NormTrace`) into a `ℂ`-linear map
`traceGamma1` for the inclusion `Γ₁(M) ⊆ Γ₁(N)` when `N ∣ M`.

This is the missing descent/trace route identified in T119 alongside
`AtkinLehner.pSupportedRaise`.  Together they compose (future work,
T121) into a same-level `p`-supported projection
`M_k(Γ₁(N)) →ₗ[ℂ] M_k(Γ₁(N))`.

## Main declarations

* `Gamma1_mapGL_isFiniteRelIndex_of_dvd` — the finite-index instance
  for `Γ₁(M).map (mapGL ℝ)` inside `Γ₁(N).map (mapGL ℝ)` when `N ∣ M`,
  built from `mapGL_injective` and the known
  `Subgroup.FiniteIndex (Gamma1 M)`.
* `traceGamma1` — the `ℂ`-linear map
  `ModularForm Γ₁(M) k →ₗ[ℂ] ModularForm Γ₁(N) k` wrapping
  `ModularForm.trace`.
* `traceGamma1_cuspForm` — the `CuspForm` variant.
* `traceGamma1_apply` — structural unfolding of the trace as
  `ModularForm.trace` applied to the input (which then unfolds via
  `ModularForm.coe_trace` to a coset sum of slash actions).

## Deliberate scope limits

* The **q-expansion coefficient formula** at the ∞ cusp
  (`(qExpansion 1 (traceGamma1 f)).coeff n = ?`) is not supplied by
  this file.  The trace averages over all cosets of `Γ₁(N) ⧸ Γ₁(M)`,
  and the coefficient at ∞ depends on which cosets stabilise that
  cusp — a distinct cusp-stabilizer calculation.  See the
  `pSupportedProjection` docstring in `AtkinLehner.lean` for the
  expected form with index normalisation.
* The **Nebentypus character transport** (relating a χ mod `M`-character
  of `f` to a χ mod `N`-character of `traceGamma1 f`) requires either
  a normality argument for `Γ₁(M)` in `Γ_0(N)` or a direct
  diamond-operator calculation on coset sums, neither of which is in
  the repo yet.

## References
* Mathlib `NumberTheory.ModularForms.NormTrace` — underlying
  `ModularForm.trace` / `CuspForm.trace` definitions.
* Diamond–Shurman §5.7 — Atkin–Lehner main-lemma trace formulation.
* Miyake §4.6 — conductor / minimal-level descent.
-/

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane OnePoint

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2.TraceOperator

/-- For a subgroup `Γ ≤ GL(2, ℝ)` with `HasDetOne`, the Möbius-action twist
`σ g` acts as the identity on `ℂ` whenever `g ∈ Γ`.  This gives
`(c • f) ∣[k] g = c • f ∣[k] g` via `ModularForm.smul_slash`. -/
private lemma σ_apply_of_mem {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    {g : GL (Fin 2) ℝ} (hg : g ∈ Γ) (c : ℂ) : UpperHalfPlane.σ g c = c := by
  show (if 0 < g.det.val then RingHom.id ℂ else starRingEnd ℂ) c = c
  rw [Subgroup.HasDetOne.det_eq hg, Units.val_one, if_pos one_pos]
  rfl

/-! ### Finite relative index instance -/

/-- For `N ∣ M` with `M ≠ 0`, `(Γ₁(M)).map (mapGL ℝ)` has finite
relative index in `(Γ₁(N)).map (mapGL ℝ)`.  This is the hypothesis
needed by `ModularForm.trace` / `CuspForm.trace`. -/
instance Gamma1_mapGL_isFiniteRelIndex_of_dvd
    {M N : ℕ} [NeZero M] (h : N ∣ M) :
    ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma1 N).map (mapGL ℝ)) where
  relIndex_ne_zero := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective]
    intro h_rel_zero
    have h_dvd : (Gamma1 M).relIndex (Gamma1 N) ∣ (Gamma1 M).index :=
      Subgroup.relIndex_dvd_index_of_le (HeckeRing.GL2.Gamma1_le_of_dvd h)
    rw [h_rel_zero] at h_dvd
    exact Subgroup.FiniteIndex.index_ne_zero (zero_dvd_iff.mp h_dvd)

/-! ### Trace linear map on `ModularForm` -/

/-- The trace operator `M_k(Γ₁(M)) →ₗ[ℂ] M_k(Γ₁(N))` for `N ∣ M`,
obtained by wrapping `ModularForm.trace` as a `ℂ`-linear map.

Concretely, for `f : ModularForm Γ₁(M) k`,

  `traceGamma1 h k f = ∑_{γ ∈ Γ₁(N) ⧸ Γ₁(M)} f ∣[k] γ⁻¹`

(as an unordered coset sum; see `ModularForm.coe_trace` for the precise
form). -/
noncomputable def traceGamma1 {M N : ℕ} [NeZero M] (h : N ∣ M) (k : ℤ) :
    ModularForm ((Gamma1 M).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) :=
    Gamma1_mapGL_isFiniteRelIndex_of_dvd h
  { toFun := fun f => ModularForm.trace ((Gamma1 N).map (mapGL ℝ)) f
    map_add' := fun f g => by
      refine DFunLike.ext _ _ fun τ => ?_
      simp only [ModularForm.coe_add, ModularForm.coe_trace, Pi.add_apply,
        Finset.sum_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      induction q using Quotient.inductionOn with
      | h r =>
        simp only [SlashInvariantForm.quotientFunc_mk, ModularForm.coe_add,
          SlashAction.add_slash, Pi.add_apply]
    map_smul' := fun c f => by
      refine DFunLike.ext _ _ fun τ => ?_
      simp only [RingHom.id_apply, ModularForm.coe_trace, ModularForm.IsGLPos.smul_apply,
        Finset.sum_apply]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      induction q using Quotient.inductionOn with
      | h r =>
        simp only [SlashInvariantForm.quotientFunc_mk, ModularForm.IsGLPos.coe_smul,
          ModularForm.smul_slash, Pi.smul_apply]
        rw [σ_apply_of_mem (Γ := (Gamma1 N).map (mapGL ℝ)) (inv_mem r.prop)] }

/-- Unfolding lemma: the underlying function of `traceGamma1 h k f` equals
`ModularForm.trace` applied to `f`.  The right-hand side then unfolds via
`ModularForm.coe_trace` to the pointwise sum of `f ∣[k] γ⁻¹` over
coset representatives `γ` of `Γ₁(N) ⧸ Γ₁(M)`. -/
lemma traceGamma1_apply {M N : ℕ} [NeZero M] (h : N ∣ M) (k : ℤ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    traceGamma1 h k f =
      haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) :=
        Gamma1_mapGL_isFiniteRelIndex_of_dvd h
      ModularForm.trace ((Gamma1 N).map (mapGL ℝ)) f := rfl

/-! ### Trace linear map on `CuspForm` -/

/-- The trace operator `S_k(Γ₁(M)) →ₗ[ℂ] S_k(Γ₁(N))` for `N ∣ M`,
obtained by wrapping `CuspForm.trace` as a `ℂ`-linear map.

The underlying ℍ → ℂ function agrees with `traceGamma1` on `M_k`: the
cusp-vanishing condition is an extra structural property preserved by
the trace (`CuspForm.trace` in Mathlib). -/
noncomputable def traceGamma1_cuspForm {M N : ℕ} [NeZero M] (h : N ∣ M) (k : ℤ) :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) :=
    Gamma1_mapGL_isFiniteRelIndex_of_dvd h
  { toFun := fun f => CuspForm.trace ((Gamma1 N).map (mapGL ℝ)) f
    map_add' := fun f g => by
      refine DFunLike.ext _ _ fun τ => ?_
      simp only [CuspForm.coe_add, CuspForm.coe_trace, Pi.add_apply,
        Finset.sum_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      induction q using Quotient.inductionOn with
      | h r =>
        simp only [SlashInvariantForm.quotientFunc_mk, CuspForm.coe_add,
          SlashAction.add_slash, Pi.add_apply]
    map_smul' := fun c f => by
      refine DFunLike.ext _ _ fun τ => ?_
      simp only [RingHom.id_apply, CuspForm.coe_trace, CuspForm.IsGLPos.smul_apply,
        Finset.sum_apply]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      induction q using Quotient.inductionOn with
      | h r =>
        simp only [SlashInvariantForm.quotientFunc_mk, CuspForm.IsGLPos.coe_smul,
          ModularForm.smul_slash, Pi.smul_apply]
        rw [σ_apply_of_mem (Γ := (Gamma1 N).map (mapGL ℝ)) (inv_mem r.prop)] }

/-! ### Infinity-fixing cosets in the trace sum (T131, deliverable I)

The trace sum unfolding `ModularForm.coe_trace` ranges over the quotient
`𝒬 := ℋ ⧸ (𝒢.subgroupOf ℋ)`, where `ℋ := (Γ₁(N)).map (mapGL ℝ)` and
`𝒢 := (Γ₁(M)).map (mapGL ℝ)`.  For the `∞`-Fourier expansion of the
trace, only those cosets whose representative fixes `∞ ∈ OnePoint ℝ`
contribute a phase-shifted copy of the input's `∞`-q-expansion (see
`AtkinLehnerProjection.lean` lines 49–109 for the cusp-geometry
discussion of T124).  This section provides the predicate and basic
API for those cosets.

Concretely, by `OnePoint.smul_infty_eq_self_iff`, a matrix `g : GL(2,ℝ)`
fixes `∞` iff `g 1 0 = 0`.  We package this at the coset level by
asking for a representative with that property — automatically
well-defined as an existential. -/

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}

/-- A coset in `ℋ ⧸ (𝒢.subgroupOf ℋ)` is **infinity-fixing** if it admits
a representative whose underlying matrix fixes `∞ : OnePoint ℝ`,
equivalently (by `OnePoint.smul_infty_eq_self_iff`) whose lower-left
entry is `0`.  This is the coset-level analogue of the local-data of
the cusp `∞` ∈ `OnePoint ℝ` for the GL-action.  By definition the
predicate is automatically well-defined (independent of representative
choice). -/
def IsInftyFixingCoset (q : ℋ ⧸ (𝒢.subgroupOf ℋ)) : Prop :=
  ∃ h : ℋ, (⟦h⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) = q ∧ (h.val : GL (Fin 2) ℝ) 1 0 = 0

/-- Characterisation of `IsInftyFixingCoset` via the `GL(2,ℝ)`-action on
`OnePoint ℝ`: a coset is infinity-fixing iff some representative `h`
satisfies `h • ∞ = ∞`.  This is the immediate translation through
`OnePoint.smul_infty_eq_self_iff`. -/
lemma isInftyFixingCoset_iff_smul_eq
    (q : ℋ ⧸ (𝒢.subgroupOf ℋ)) :
    IsInftyFixingCoset q ↔
      ∃ h : ℋ, (⟦h⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) = q ∧
        (h.val : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ) = ∞ :=
  ⟨fun ⟨h, hq, h10⟩ => ⟨h, hq, OnePoint.smul_infty_eq_self_iff.mpr h10⟩,
   fun ⟨h, hq, hsmul⟩ => ⟨h, hq, OnePoint.smul_infty_eq_self_iff.mp hsmul⟩⟩

/-- The identity coset is infinity-fixing: the identity matrix has
`(1 : GL(2,ℝ)) 1 0 = 0`, so `1 ∈ ℋ` witnesses the existential. -/
lemma isInftyFixingCoset_one :
    IsInftyFixingCoset (⟦(1 : ℋ)⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) :=
  ⟨1, rfl, by simp⟩

/-- Existence form: there is at least one infinity-fixing coset, namely
the identity coset.  This is the basic non-emptiness statement
underlying the period-1 trace `q`-expansion formula:  the trace sum
always contains at least one term whose representative fixes `∞`,
contributing a phase-shifted copy of the input's `∞`-q-expansion. -/
lemma exists_isInftyFixingCoset :
    ∃ q : ℋ ⧸ (𝒢.subgroupOf ℋ), IsInftyFixingCoset q :=
  ⟨_, isInftyFixingCoset_one⟩

/-- Specialisation to the trace-relevant pair
`ℋ = (Γ₁(N)).map (mapGL ℝ)`, `𝒢 = (Γ₁(M)).map (mapGL ℝ)`: the identity
coset is infinity-fixing.  This is the concrete starting point for the
period-1 trace `q`-expansion formula at the inclusion
`(Γ₁(M)).map (mapGL ℝ) ≤ (Γ₁(N)).map (mapGL ℝ)` (e.g. `M = p · N`). -/
lemma isInftyFixingCoset_one_Gamma1
    {M N : ℕ} :
    IsInftyFixingCoset
      (𝒢 := (Gamma1 M).map (mapGL ℝ))
      (ℋ := (Gamma1 N).map (mapGL ℝ))
      (⟦(1 : ↥((Gamma1 N).map (mapGL ℝ)))⟧) :=
  isInftyFixingCoset_one

/-! ### Splitting the trace sum by `IsInftyFixingCoset` (T131, deliverable I)

`ModularForm.coe_trace` unfolds the trace as `∑ q, quotientFunc f q` over
`𝒬 = ℋ ⧸ (𝒢.subgroupOf ℋ)`.  The following purely structural decomposition
splits that sum into the infinity-fixing and non-infinity-fixing parts via
`Finset.sum_filter_add_sum_filter_not`.  No claim is made that the
non-fixing part vanishes — that is a stronger cusp-stabilizer statement
deferred to a future ticket. -/

open scoped Classical in
/-- Pointwise split of the `ModularForm` trace sum by `IsInftyFixingCoset`.
This is purely the partitioning of `Finset.univ : Finset 𝒬` into the
infinity-fixing cosets and their complement; the per-coset summands are
unchanged. -/
theorem traceGamma1_apply_split_inftyFixing
    {M N : ℕ} [NeZero M] (h : N ∣ M) (k : ℤ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (τ : ℍ) :
    haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex
        ((Gamma1 N).map (mapGL ℝ)) := Gamma1_mapGL_isFiniteRelIndex_of_dvd h
    haveI hFin : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
        ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
      Fintype.ofFinite _
    (traceGamma1 h k f : ℍ → ℂ) τ =
      (∑ q ∈ (@Finset.univ _ hFin).filter
          (IsInftyFixingCoset (𝒢 := (Gamma1 M).map (mapGL ℝ))
            (ℋ := (Gamma1 N).map (mapGL ℝ))),
          SlashInvariantForm.quotientFunc f q τ) +
      (∑ q ∈ (@Finset.univ _ hFin).filter
          (fun q => ¬ IsInftyFixingCoset
            (𝒢 := (Gamma1 M).map (mapGL ℝ))
            (ℋ := (Gamma1 N).map (mapGL ℝ)) q),
          SlashInvariantForm.quotientFunc f q τ) := by
  haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma1 N).map (mapGL ℝ)) := Gamma1_mapGL_isFiniteRelIndex_of_dvd h
  haveI : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
      ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
    Fintype.ofFinite _
  show (ModularForm.trace ((Gamma1 N).map (mapGL ℝ)) f : ℍ → ℂ) τ = _
  rw [ModularForm.coe_trace, Finset.sum_apply]
  convert (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm using 2

open scoped Classical in
/-- `CuspForm` analogue of `traceGamma1_apply_split_inftyFixing`: the same
pointwise split through `CuspForm.coe_trace`. -/
theorem traceGamma1_cuspForm_apply_split_inftyFixing
    {M N : ℕ} [NeZero M] (h : N ∣ M) (k : ℤ)
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (τ : ℍ) :
    haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex
        ((Gamma1 N).map (mapGL ℝ)) := Gamma1_mapGL_isFiniteRelIndex_of_dvd h
    haveI hFin : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
        ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
      Fintype.ofFinite _
    (traceGamma1_cuspForm h k f : ℍ → ℂ) τ =
      (∑ q ∈ (@Finset.univ _ hFin).filter
          (IsInftyFixingCoset (𝒢 := (Gamma1 M).map (mapGL ℝ))
            (ℋ := (Gamma1 N).map (mapGL ℝ))),
          SlashInvariantForm.quotientFunc f q τ) +
      (∑ q ∈ (@Finset.univ _ hFin).filter
          (fun q => ¬ IsInftyFixingCoset
            (𝒢 := (Gamma1 M).map (mapGL ℝ))
            (ℋ := (Gamma1 N).map (mapGL ℝ)) q),
          SlashInvariantForm.quotientFunc f q τ) := by
  haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma1 N).map (mapGL ℝ)) := Gamma1_mapGL_isFiniteRelIndex_of_dvd h
  haveI : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
      ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
    Fintype.ofFinite _
  show (CuspForm.trace ((Gamma1 N).map (mapGL ℝ)) f : ℍ → ℂ) τ = _
  rw [CuspForm.coe_trace, Finset.sum_apply]
  convert (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm using 2

/-! ### Identity-coset isolation (T131, deliverable I extension)

The identity coset `⟦1⟧` is a member of the infinity-fixing filter
(by `isInftyFixingCoset_one`).  Combined with `Finset.add_sum_erase`,
this lets us split the infinity-fixing block of the trace sum into
the identity-coset summand plus a sum over the remaining
infinity-fixing cosets, yielding a 3-way decomposition. -/

open scoped Classical in
/-- The identity coset `⟦1⟧` is a member of the (filtered) infinity-fixing
finset.  Reusable across `ModularForm` and `CuspForm` 3-way splits. -/
lemma identity_mem_inftyFixing_filter
    (𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)) [Fintype (ℋ ⧸ (𝒢.subgroupOf ℋ))]
    [DecidablePred (IsInftyFixingCoset (𝒢 := 𝒢) (ℋ := ℋ))] :
    (⟦(1 : ℋ)⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) ∈
      (Finset.univ : Finset _).filter
        (IsInftyFixingCoset (𝒢 := 𝒢) (ℋ := ℋ)) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, isInftyFixingCoset_one⟩

/-- `Gamma1`-specialised convenience: the identity coset of
`(Γ₁(N)).map (mapGL ℝ) ⧸ ((Γ₁(M)).map (mapGL ℝ)).subgroupOf _` is in
the infinity-fixing filter. -/
lemma identity_mem_inftyFixing_filter_Gamma1
    {M N : ℕ} [Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
      ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ)))]
    [DecidablePred (IsInftyFixingCoset (𝒢 := (Gamma1 M).map (mapGL ℝ))
      (ℋ := (Gamma1 N).map (mapGL ℝ)))] :
    (⟦(1 : ↥((Gamma1 N).map (mapGL ℝ)))⟧ :
        (Gamma1 N).map (mapGL ℝ) ⧸
          ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) ∈
      (Finset.univ : Finset _).filter
        (IsInftyFixingCoset (𝒢 := (Gamma1 M).map (mapGL ℝ))
          (ℋ := (Gamma1 N).map (mapGL ℝ))) :=
  identity_mem_inftyFixing_filter _ _

open scoped Classical in
/-- 3-way pointwise split of the `ModularForm` trace coset sum:
identity-coset summand + remaining infinity-fixing cosets + non-fixing
cosets.  Pure partitioning — no claim of vanishing or coefficient
identity. -/
theorem traceGamma1_apply_three_way_split
    {M N : ℕ} [NeZero M] (h : N ∣ M) (k : ℤ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (τ : ℍ) :
    haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex
        ((Gamma1 N).map (mapGL ℝ)) := Gamma1_mapGL_isFiniteRelIndex_of_dvd h
    haveI hFin : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
        ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
      Fintype.ofFinite _
    (traceGamma1 h k f : ℍ → ℂ) τ =
      SlashInvariantForm.quotientFunc f
        (⟦(1 : ↥((Gamma1 N).map (mapGL ℝ)))⟧) τ +
      (∑ q ∈ ((@Finset.univ _ hFin).filter
            (IsInftyFixingCoset (𝒢 := (Gamma1 M).map (mapGL ℝ))
              (ℋ := (Gamma1 N).map (mapGL ℝ)))).erase
            (⟦(1 : ↥((Gamma1 N).map (mapGL ℝ)))⟧),
          SlashInvariantForm.quotientFunc f q τ) +
      (∑ q ∈ (@Finset.univ _ hFin).filter
          (fun q => ¬ IsInftyFixingCoset
            (𝒢 := (Gamma1 M).map (mapGL ℝ))
            (ℋ := (Gamma1 N).map (mapGL ℝ)) q),
          SlashInvariantForm.quotientFunc f q τ) := by
  haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma1 N).map (mapGL ℝ)) := Gamma1_mapGL_isFiniteRelIndex_of_dvd h
  haveI hFin : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
      ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
    Fintype.ofFinite _
  rw [traceGamma1_apply_split_inftyFixing h k f τ]
  congr 1
  have hmem :
      (⟦(1 : ↥((Gamma1 N).map (mapGL ℝ)))⟧ :
        (Gamma1 N).map (mapGL ℝ) ⧸
          ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) ∈
      (@Finset.univ _
          (Fintype.ofFinite ((Gamma1 N).map (mapGL ℝ) ⧸
            ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))))).filter
        (IsInftyFixingCoset (𝒢 := (Gamma1 M).map (mapGL ℝ))
          (ℋ := (Gamma1 N).map (mapGL ℝ))) :=
    Finset.mem_filter.mpr
      ⟨@Finset.mem_univ _
          (Fintype.ofFinite ((Gamma1 N).map (mapGL ℝ) ⧸
            ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ)))) _,
        isInftyFixingCoset_one⟩
  exact (Finset.add_sum_erase _ (fun q => SlashInvariantForm.quotientFunc f q τ) hmem).symm

open scoped Classical in
/-- `CuspForm` analogue of `traceGamma1_apply_three_way_split`. -/
theorem traceGamma1_cuspForm_apply_three_way_split
    {M N : ℕ} [NeZero M] (h : N ∣ M) (k : ℤ)
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (τ : ℍ) :
    haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex
        ((Gamma1 N).map (mapGL ℝ)) := Gamma1_mapGL_isFiniteRelIndex_of_dvd h
    haveI hFin : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
        ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
      Fintype.ofFinite _
    (traceGamma1_cuspForm h k f : ℍ → ℂ) τ =
      SlashInvariantForm.quotientFunc f
        (⟦(1 : ↥((Gamma1 N).map (mapGL ℝ)))⟧) τ +
      (∑ q ∈ ((@Finset.univ _ hFin).filter
            (IsInftyFixingCoset (𝒢 := (Gamma1 M).map (mapGL ℝ))
              (ℋ := (Gamma1 N).map (mapGL ℝ)))).erase
            (⟦(1 : ↥((Gamma1 N).map (mapGL ℝ)))⟧),
          SlashInvariantForm.quotientFunc f q τ) +
      (∑ q ∈ (@Finset.univ _ hFin).filter
          (fun q => ¬ IsInftyFixingCoset
            (𝒢 := (Gamma1 M).map (mapGL ℝ))
            (ℋ := (Gamma1 N).map (mapGL ℝ)) q),
          SlashInvariantForm.quotientFunc f q τ) := by
  haveI : ((Gamma1 M).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma1 N).map (mapGL ℝ)) := Gamma1_mapGL_isFiniteRelIndex_of_dvd h
  haveI hFin : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
      ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
    Fintype.ofFinite _
  rw [traceGamma1_cuspForm_apply_split_inftyFixing h k f τ]
  congr 1
  have hmem :
      (⟦(1 : ↥((Gamma1 N).map (mapGL ℝ)))⟧ :
        (Gamma1 N).map (mapGL ℝ) ⧸
          ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) ∈
      (@Finset.univ _
          (Fintype.ofFinite ((Gamma1 N).map (mapGL ℝ) ⧸
            ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))))).filter
        (IsInftyFixingCoset (𝒢 := (Gamma1 M).map (mapGL ℝ))
          (ℋ := (Gamma1 N).map (mapGL ℝ))) :=
    Finset.mem_filter.mpr
      ⟨@Finset.mem_univ _
          (Fintype.ofFinite ((Gamma1 N).map (mapGL ℝ) ⧸
            ((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ)))) _,
        isInftyFixingCoset_one⟩
  exact (Finset.add_sum_erase _ (fun q => SlashInvariantForm.quotientFunc f q τ) hmem).symm

/-! ### Next-theorem signature

The same-level `p`-supported projection (T121, future work) is

```lean
noncomputable def pSupportedProjection {N : ℕ} [NeZero N] (k : ℤ)
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (traceGamma1 (Nat.dvd_mul_left N p) k).comp
    (HeckeRing.GL2.AtkinLehner.pSupportedRaise k p hp hpN)
```

which by construction lives at `M_k(Γ₁(N))`.  Its period-1 q-expansion
coefficient and Nebentypus character compatibility are **not** direct
consequences of `traceGamma1_apply` — both require a further
cusp-stabilizer / coset calculation — so they are deferred to a
dedicated ticket. -/

end HeckeRing.GL2.TraceOperator
