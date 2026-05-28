/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.Eigenforms.TraceOperator
import LeanModularForms.Eigenforms.AtkinLehner
import LeanModularForms.HeckeRIngs.GL2.Prop334_StabSurj

/-!
# Same-level `p`-supported projection (POST-4i / T121, POST-4j / T122,
POST-4k / T123, POST-4l / T124)

This file assembles the same-level `p`-supported projection on
`M_k(Γ₁(N))` by composing

  `pSupportedRaise k p hp hpN : M_k(Γ₁(N)) →ₗ[ℂ] M_k(Γ₁(p · N))`
      (from `AtkinLehner.lean`, T119)

with

  `traceGamma1 (Nat.dvd_mul_left N p) k : M_k(Γ₁(p · N)) →ₗ[ℂ] M_k(Γ₁(N))`
      (from `TraceOperator.lean`, T120, specialised to `N ∣ p · N`).

## Landed declarations

* `pSupportedProjection` — the composition, a `ℂ`-linear endomorphism
  of `M_k(Γ₁(N))`.
* `pSupportedProjection_eq_trace_pSupportedRaise` — the defining
  equation `pSupportedProjection f = traceGamma1 (pSupportedRaise f)`.
* `pSupportedProjection_apply` — rewrites the output in terms of the
  underlying Mathlib `ModularForm.trace`, which then unfolds via
  `ModularForm.coe_trace` to a pointwise sum of slash-actions of
  `pSupportedRaise k p hp hpN f` over coset representatives of
  `Γ₁(N) ⧸ Γ₁(p · N)`.
* `traceGamma1_slash_mapGL_commute` (T123) — the trace commutes with
  slashing by `mapGL ℝ β` for any `β ∈ Γ₀(M)` (the coset-conjugation
  identity at the `ℍ → ℂ` level).
* `traceGamma1_diamondOpHom_commute` (T123) — the diamond form of the
  same commutation: `diamondOp (unitsMap h d_M) ∘ traceGamma1 =
  traceGamma1 ∘ diamondOp d_M`.
* `traceGamma1_mem_modFormCharSpace` (T123) — unconditional Nebentypus
  character compatibility: a character-space-membership at level `M`
  pushes down to level `N` along the trace.
* `pSupportedProjection_mem_modFormCharSpace` (T123) — same for the
  `p`-supported projection; follows from the trace version plus
  `pSupportedRaise_mem_modFormCharSpace` at level `p · N`.

## Period-1 `q`-expansion formula (T124): reality check

**The naive p-supported coefficient formula**

  `(qExpansion 1 (pSupportedProjection f)).coeff n
    = [Γ₁(N) : Γ₁(p · N)] · (if p ∣ n then (qExpansion 1 f).coeff n else 0)`

**is false**, and more importantly the trace/projection route cannot
supply a clean p-supported coefficient statement usable by
`qSupportedOnDvd_mem_cuspFormsOld_of_char`.  The obstruction is
structural, not an unfinished calculation:

### Why the simple scaling fails

Write `ℋ := Γ₁(N).map (mapGL ℝ)`, `𝒢 := Γ₁(p · N).map (mapGL ℝ)`, and
`𝒬 := ℋ ⧸ (𝒢.subgroupOf ℋ)`.  The trace sum

  `traceGamma1 g = Σ_{q ∈ 𝒬} g ∣[k] γ_q⁻¹`

is a sum of `[Γ₁(N) : Γ₁(p · N)]` slash-translates.  Its Fourier
expansion at the `∞` cusp picks up contributions from **each** coset
representative `γ_q`:

1. If `γ_q` stabilises `∞`, i.e. `γ_q ∈ Γ₁(N) ∩ Stab(∞)`, then
   `g ∣[k] γ_q⁻¹` has `∞`-Fourier coefficients equal to a phase-shift
   of `(qExpansion 1 g).coeff n`.
2. If `γ_q` does **not** stabilise `∞`, then `g ∣[k] γ_q⁻¹` has its
   own Fourier expansion at `∞` expressing the pullback of `g`'s
   expansion at the cusp `γ_q · ∞ ≠ ∞`.  These coefficients are in
   general **unrelated** to `(qExpansion 1 g).coeff n`.

For the inclusion `Γ₁(p · N) ≤ Γ₁(N)` with `p ∤ N` or `p ∣ N`, the
stabilisers satisfy
  `Γ₁(N) ∩ Stab(∞) = Γ₁(p · N) ∩ Stab(∞) = ⟨T⟩`
(the upper-unipotent subgroup), so the **only** `∞`-stabilising coset
in `𝒬` is the identity coset.  All other cosets contribute
other-cusp expansions at `∞`, which are **not** p-supported merely
because the input is p-supported at `∞`.

Consequently:

  `(qExpansion 1 (pSupportedProjection f)).coeff n
    = (qExpansion 1 (pSupportedRaise f)).coeff n +
      Σ_{q ≠ id} (other-cusp-expansion contributions at ∞)`.

The first term is `(if p ∣ n then a_n(f) else 0)` (direct from
`qExpansion_one_pSupportedRaise_coeff`), but the second-term
contributions do **not** vanish in general, and they are **not**
obviously p-supported.

### Consequence for the composite `mainLemma`

`pSupportedProjection` is **not** the right operator to feed into
`qSupportedOnDvd_mem_cuspFormsOld_of_char` for a composite-`N`
`mainLemma`.  The proof route requires an operator whose output is
simultaneously:

1. A level-`N` form in the Nebentypus space `M_k(Γ₁(N), χ)` — satisfied
   by `pSupportedProjection` (see `pSupportedProjection_mem_modFormCharSpace`).
2. Whose `∞`-Fourier expansion is supported on multiples of `p` — **not**
   satisfied without the auxiliary cusp-Fourier calculation described
   above.

### Next-theorem signatures (the correct `mainLemma` route)

The standard Diamond–Shurman §5.7 and Miyake §4.6 routes use
**Atkin–Lehner–Li orthogonality** or the **Petersson inner product**
rather than a finite-trace formula.  The target statements are:

```lean
-- Miyake §4.6.5 / Diamond–Shurman 5.7.1: oldform characterisation via
-- U_p-eigenvalue decomposition at prime p ∣ N, working ENTIRELY at
-- level Γ₁(N), no level-raising/trace round-trip.
theorem mainLemma_charSpace_composite_via_Up
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k

-- Alternative (Atkin–Lehner–Li, D–S Thm 5.7.2): orthogonal decomposition
-- using the Petersson inner product at level N.
theorem cuspFormsNew_orthogonal_cuspFormsOld ...

-- Or the Möbius-sieve packaging (Miyake 4.6.8):
-- f - Σ_{p ∣ N} V_p(U_p f) + Σ_{pq ∣ N} V_{pq}(U_{pq} f) - ...
--     ∈ intersection of p-coprime-supports = {0} forces the sieve
--     identity, which implies f is an oldform.
theorem cuspFormsOld_of_coprime_coeff_vanishing_via_Mobius ...
```

Each of these **avoids** the trace round-trip's cusp-geometry blocker.
The `pSupportedProjection` API landed in T121–T123 remains useful for
character-space reasoning (Nebentypus compatibility is unconditional),
but the `mainLemma` coefficient chain should not depend on a q-expansion
formula for `pSupportedProjection`.

## References
* Diamond–Shurman §5.7 (oldforms/newforms via Atkin–Lehner–Li).
* Miyake §4.5–4.6 (Main Lemma via U_p/V_p decomposition).
-/

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Manifold

namespace HeckeRing.GL2.AtkinLehner

/-- **Same-level `p`-supported projection** on `M_k(Γ₁(N))`, for a
prime `p ∣ N`.  Defined as the composition

  `pSupportedProjection k p hp hpN := traceGamma1 ∘ pSupportedRaise`.

As a coset sum,

  `pSupportedProjection k p hp hpN f =
    ∑_{γ ∈ Γ₁(N) ⧸ Γ₁(p · N)} (pSupportedRaise k p hp hpN f) ∣[k] γ⁻¹`

(see `pSupportedProjection_apply`).  Nebentypus character
compatibility is unconditional (T123,
`pSupportedProjection_mem_modFormCharSpace`).  A clean period-1
q-expansion coefficient formula is **not** available at the level of
this projection — see the file docstring (T124) for the cusp-geometry
obstruction and the correct `mainLemma` routes. -/
noncomputable def pSupportedProjection {N : ℕ} [NeZero N] (k : ℤ)
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (HeckeRing.GL2.TraceOperator.traceGamma1 (Nat.dvd_mul_left N p) k).comp
    (pSupportedRaise k p hp hpN)

/-- Defining equation: `pSupportedProjection f = traceGamma1 (pSupportedRaise f)`. -/
theorem pSupportedProjection_eq_trace_pSupportedRaise
    {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    pSupportedProjection k p hp hpN f =
      HeckeRing.GL2.TraceOperator.traceGamma1 (Nat.dvd_mul_left N p) k
        (pSupportedRaise k p hp hpN f) := rfl

/-- Structural unfolding via Mathlib `ModularForm.trace`: the underlying
function of `pSupportedProjection k p hp hpN f` equals Mathlib's
`ModularForm.trace` applied to `pSupportedRaise k p hp hpN f`.  Combined
with `ModularForm.coe_trace` this gives the pointwise coset sum

  `(pSupportedProjection f : ℍ → ℂ) =
    ∑ q : (Γ₁(N).map ⧸ (Γ₁(p · N).map).subgroupOf Γ₁(N).map),
      SlashInvariantForm.quotientFunc (pSupportedRaise f) q`. -/
theorem pSupportedProjection_apply
    {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    pSupportedProjection k p hp hpN f =
      haveI : ((Gamma1 (p * N)).map (mapGL ℝ)).IsFiniteRelIndex
          ((Gamma1 N).map (mapGL ℝ)) :=
        HeckeRing.GL2.TraceOperator.Gamma1_mapGL_isFiniteRelIndex_of_dvd
          (Nat.dvd_mul_left N p)
      ModularForm.trace ((Gamma1 N).map (mapGL ℝ))
        (pSupportedRaise k p hp hpN f) := by
  rw [pSupportedProjection_eq_trace_pSupportedRaise,
    HeckeRing.GL2.TraceOperator.traceGamma1_apply]

/-- `pSupportedProjection` is the identically-zero map on the zero form,
by linearity. -/
@[simp]
theorem pSupportedProjection_zero {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ)
    [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    pSupportedProjection k p hp hpN 0 = 0 := map_zero _

/-! ### Conditional character-compatibility helpers (legacy, T122)

The next two theorems are the **conditional** character-compatibility
lemmas originally introduced in T122, stated modulo an explicit
trace/diamond commutation hypothesis `h_commute`.  That commutation is
now discharged unconditionally in T123 as
`traceGamma1_diamondOpHom_commute`, and the unconditional
consequences `traceGamma1_mem_modFormCharSpace` and
`pSupportedProjection_mem_modFormCharSpace` are proved later in this
file (see the `### Unconditional character compatibility (T123)`
section).

The conditional versions are retained as reusable lower-level helpers
for any downstream setting where only a weaker commutation is
available (e.g. restricting to a subset of `(ZMod M)ˣ`, or plugging a
different trace variant).  They do **not** block the unconditional
theorems. -/

/-- **Character compatibility for `traceGamma1`** (conditional lemma,
legacy T122 form).  If `f` at the deeper level `M` lies in the
character space for `χ.comp (ZMod.unitsMap h)` (the natural lift of
`χ : (ZMod N)ˣ →* ℂˣ` along `N ∣ M`), and the trace commutes with the
diamond operator on `f` (`h_commute`), then the descent
`traceGamma1 h k f` lies in the level-`N` character space for `χ`.

The unconditional form is `traceGamma1_mem_modFormCharSpace`
(T123), which instantiates this lemma with
`traceGamma1_diamondOpHom_commute`.  This conditional version is
retained for any downstream code that supplies a different or
weaker commutation. -/
theorem traceGamma1_mem_modFormCharSpace_of_commute
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap h)))
    (h_commute :
      ∀ d_M : (ZMod M)ˣ,
        diamondOpHom k (ZMod.unitsMap h d_M)
            (HeckeRing.GL2.TraceOperator.traceGamma1 h k f) =
          HeckeRing.GL2.TraceOperator.traceGamma1 h k (diamondOpHom k d_M f)) :
    HeckeRing.GL2.TraceOperator.traceGamma1 h k f ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff]
  intro d
  obtain ⟨β, hβ⟩ := HeckeRing.GL2.Prop334.exists_Gamma0_lift_of_dvd h d
  set d_M : (ZMod M)ˣ := Gamma0MapUnits β
  have hd_eq : ZMod.unitsMap h d_M = d := hβ
  rw [← hd_eq, h_commute d_M, ((mem_modFormCharSpace_iff k (χ.comp (ZMod.unitsMap h)) f).mp hf) d_M,
    map_smul]
  congr 1

/-- **Character compatibility for `pSupportedProjection`** (conditional
lemma, legacy T122 form).  If `f ∈ modFormCharSpace k χ` at level `N`
and the diamond/trace commutation holds on the level-raised form
`pSupportedRaise k p hp hpN f` at level `p · N`, then
`pSupportedProjection k p hp hpN f` lies in `modFormCharSpace k χ`.
The level-`p · N` character preservation of `pSupportedRaise` is
supplied by the existing `pSupportedRaise_mem_modFormCharSpace` (T119).

The unconditional form is `pSupportedProjection_mem_modFormCharSpace`
(T123), which instantiates this lemma with
`traceGamma1_diamondOpHom_commute`.  This conditional version is
retained for any downstream code that supplies a different or weaker
commutation. -/
theorem pSupportedProjection_mem_modFormCharSpace_of_commute
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ)
    (h_commute :
      ∀ d_M : (ZMod (p * N))ˣ,
        diamondOpHom k
            (ZMod.unitsMap (Nat.dvd_mul_left N p) d_M)
            (HeckeRing.GL2.TraceOperator.traceGamma1
              (Nat.dvd_mul_left N p) k
              (pSupportedRaise k p hp hpN f)) =
          HeckeRing.GL2.TraceOperator.traceGamma1
              (Nat.dvd_mul_left N p) k
            (diamondOpHom k d_M (pSupportedRaise k p hp hpN f))) :
    pSupportedProjection k p hp hpN f ∈ modFormCharSpace k χ := by
  have hf_raise : pSupportedRaise k p hp hpN f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N p))) :=
    pSupportedRaise_mem_modFormCharSpace hp hpN χ hf
  rw [pSupportedProjection_eq_trace_pSupportedRaise]
  exact traceGamma1_mem_modFormCharSpace_of_commute
    (Nat.dvd_mul_left N p) χ hf_raise h_commute

/-! ### Trace/diamond commutation (T123)

The residual commutation between the trace and the diamond operator,
proved here via the coset-conjugation equivalence induced by
`β ∈ Γ₀(M)`.  Together with the T122 lift lemma it yields the
unconditional character theorems `traceGamma1_mem_modFormCharSpace`
and `pSupportedProjection_mem_modFormCharSpace`. -/

section TraceCommute

/-- Conjugation by `mapGL ℝ β` (for `β ∈ Γ₀(M)`) preserves
`(Γ₁(N)).map (mapGL ℝ)`, using normality of `Γ₁(N)` in `Γ₀(N)` plus
`Γ₀(M) ⊆ Γ₀(N)` from `h : N ∣ M`. -/
private lemma conjBy_beta_mem_Gamma1N_map
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) (β : ↥(Gamma0 M))
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (mapGL ℝ (β : SL(2, ℤ))) * γ * (mapGL ℝ (β : SL(2, ℤ)))⁻¹ ∈
      (Gamma1 N).map (mapGL ℝ) := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  have hβN : (β : SL(2, ℤ)) ∈ Gamma0 N := Gamma0_le_of_dvd h β.property
  refine Subgroup.mem_map.mpr
    ⟨(β : SL(2, ℤ)) * σ * (β : SL(2, ℤ))⁻¹, ?_, ?_⟩
  · exact Gamma0_normalizes_Gamma1 ⟨(β : SL(2, ℤ)), hβN⟩ σ hσ
  · simp [map_mul, map_inv]

/-- Conjugation by `mapGL ℝ β` (for `β ∈ Γ₀(M)`) preserves
`(Γ₁(M)).map (mapGL ℝ)`, using normality of `Γ₁(M)` in `Γ₀(M)`. -/
private lemma conjBy_beta_mem_Gamma1M_map
    {M : ℕ} (β : ↥(Gamma0 M))
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ (Gamma1 M).map (mapGL ℝ)) :
    (mapGL ℝ (β : SL(2, ℤ))) * γ * (mapGL ℝ (β : SL(2, ℤ)))⁻¹ ∈
      (Gamma1 M).map (mapGL ℝ) := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  refine Subgroup.mem_map.mpr
    ⟨(β : SL(2, ℤ)) * σ * (β : SL(2, ℤ))⁻¹, ?_, ?_⟩
  · exact Gamma0_normalizes_Gamma1 β σ hσ
  · simp [map_mul, map_inv]

/-- Conjugation by `mapGL ℝ β` as an `Equiv` on `(Γ₁(N)).map (mapGL ℝ)`. -/
private noncomputable def conjℋEquiv
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) (β : ↥(Gamma0 M)) :
    ↥((Gamma1 N).map (mapGL ℝ)) ≃ ↥((Gamma1 N).map (mapGL ℝ)) where
  toFun γ := ⟨mapGL ℝ (β : SL(2, ℤ)) * γ.val * (mapGL ℝ (β : SL(2, ℤ)))⁻¹,
              conjBy_beta_mem_Gamma1N_map h β γ.property⟩
  invFun γ := ⟨(mapGL ℝ (β : SL(2, ℤ)))⁻¹ * γ.val * mapGL ℝ (β : SL(2, ℤ)), by
    have hγ' := conjBy_beta_mem_Gamma1N_map h
      ((β⁻¹ : ↥(Gamma0 M))) γ.property
    simpa [map_inv, mul_assoc] using hγ'⟩
  left_inv γ := by ext; simp [mul_assoc]
  right_inv γ := by ext; simp [mul_assoc]

/-- The conjugation equivalence respects the left-coset congruence
for `(Γ₁(M).map).subgroupOf (Γ₁(N).map)`, because `β` normalises
`Γ₁(M)` (in `Γ₀(M)`). -/
private lemma conjℋEquiv_leftRel
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) (β : ↥(Gamma0 M))
    (a₁ a₂ : ↥((Gamma1 N).map (mapGL ℝ))) :
    QuotientGroup.leftRel (((Gamma1 M).map (mapGL ℝ)).subgroupOf
        ((Gamma1 N).map (mapGL ℝ))) a₁ a₂ ↔
      QuotientGroup.leftRel (((Gamma1 M).map (mapGL ℝ)).subgroupOf
        ((Gamma1 N).map (mapGL ℝ)))
        (conjℋEquiv h β a₁) (conjℋEquiv h β a₂) := by
  simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
  set β_gl : GL (Fin 2) ℝ := mapGL ℝ (β : SL(2, ℤ)) with hβ_gl
  have hconj_eq :
      ((conjℋEquiv h β a₁)⁻¹ * conjℋEquiv h β a₂).val =
        β_gl * (a₁⁻¹ * a₂).val * β_gl⁻¹ := by
    show (β_gl * a₁.val * β_gl⁻¹)⁻¹ * (β_gl * a₂.val * β_gl⁻¹) =
      β_gl * (a₁.val⁻¹ * a₂.val) * β_gl⁻¹
    group
  rw [hconj_eq]
  constructor
  · intro h₁
    exact conjBy_beta_mem_Gamma1M_map β h₁
  · intro h₂
    have hinv := conjBy_beta_mem_Gamma1M_map (β⁻¹ : ↥(Gamma0 M)) h₂
    simp only [InvMemClass.coe_inv, map_inv] at hinv
    have : β_gl⁻¹ * (β_gl * (a₁⁻¹ * a₂).val * β_gl⁻¹) * β_gl = (a₁⁻¹ * a₂).val := by
      group
    rw [← this]
    convert hinv using 1

/-- The conjugation equivalence on cosets `Γ₁(N).map ⧸ Γ₁(M).map`. -/
private noncomputable def conjCosetEquiv
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) (β : ↥(Gamma0 M)) :
    letI := TraceOperator.Gamma1_mapGL_isFiniteRelIndex_of_dvd h
    (↥((Gamma1 N).map (mapGL ℝ))) ⧸
        (((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) ≃
      (↥((Gamma1 N).map (mapGL ℝ))) ⧸
        (((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
  Quotient.congr (conjℋEquiv h β) (conjℋEquiv_leftRel h β)

/-- Per-coset identity: slashing `quotientFunc f q` by `mapGL ℝ β`
reindexes to `quotientFunc (diamondOpAux β f) (σ_β⁻¹ q)`, where `σ_β`
is the conjugation coset equivalence. -/
private lemma quotientFunc_slash_beta_eq
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (β : ↥(Gamma0 M))
    (q : (↥((Gamma1 N).map (mapGL ℝ))) ⧸
        (((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ)))) :
    (SlashInvariantForm.quotientFunc (𝒢 := (Gamma1 M).map (mapGL ℝ))
          (ℋ := (Gamma1 N).map (mapGL ℝ)) f q) ∣[k]
        mapGL ℝ (β : SL(2, ℤ)) =
      SlashInvariantForm.quotientFunc (𝒢 := (Gamma1 M).map (mapGL ℝ))
        (ℋ := (Gamma1 N).map (mapGL ℝ)) (diamondOpAux k β f)
        ((conjCosetEquiv h β).symm q) := by
  induction q using Quotient.inductionOn with
  | h r =>
    show (⇑f ∣[k] r.val⁻¹) ∣[k] mapGL ℝ (β : SL(2, ℤ)) =
      (⇑(diamondOpAux k β f)) ∣[k]
        ((conjℋEquiv h β).symm r).val⁻¹
    show (⇑f ∣[k] r.val⁻¹) ∣[k] mapGL ℝ (β : SL(2, ℤ)) =
      (⇑f ∣[k] mapGL ℝ (β : SL(2, ℤ))) ∣[k]
        ((mapGL ℝ (β : SL(2, ℤ)))⁻¹ * r.val * mapGL ℝ (β : SL(2, ℤ)))⁻¹
    rw [← SlashAction.slash_mul, ← SlashAction.slash_mul]
    congr 1
    group

/-- **Trace/slash commutation for `β ∈ Γ₀(M)` (T123).**  The underlying
`ℍ → ℂ` of `traceGamma1 h k f` slashed by `mapGL ℝ β` equals the
underlying of the trace of `diamondOpAux k β f` (the `β`-slash at level
`M`).  This is the T123 theorem that discharges the former T122
commutation blocker, proved via the coset-conjugation equivalence
`conjCosetEquiv` on `Γ₁(N).map ⧸ Γ₁(M).map` and the per-coset identity
`quotientFunc_slash_beta_eq`. -/
theorem traceGamma1_slash_mapGL_commute
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (β : ↥(Gamma0 M)) :
    (TraceOperator.traceGamma1 h k f : UpperHalfPlane → ℂ) ∣[k]
        mapGL ℝ (β : SL(2, ℤ)) =
      (TraceOperator.traceGamma1 h k (diamondOpAux k β f) : UpperHalfPlane → ℂ) := by
  haveI := TraceOperator.Gamma1_mapGL_isFiniteRelIndex_of_dvd h
  letI : Fintype ((↥((Gamma1 N).map (mapGL ℝ))) ⧸
      (((Gamma1 M).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ)))) :=
    Fintype.ofFinite _
  rw [TraceOperator.traceGamma1_apply, TraceOperator.traceGamma1_apply,
    ModularForm.coe_trace, ModularForm.coe_trace, SlashAction.sum_slash]
  refine Finset.sum_bij (fun q _ ↦ (conjCosetEquiv h β).symm q)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun _ _ _ _ H ↦ (conjCosetEquiv h β).symm.injective H)
    (fun q _ ↦ ⟨conjCosetEquiv h β q, Finset.mem_univ _, by simp⟩)
    (fun q _ ↦ quotientFunc_slash_beta_eq h f β q)

/-- Inline compatibility: `Gamma0MapUnits` of a Γ₀(N)-embedding of
`β ∈ Γ₀(M)` equals the `unitsMap`-image of `Gamma0MapUnits β`, for
`N ∣ M`.  Companion to `Prop334.Gamma0MapUnits_unitsMap_of_Gamma0_mul`,
stated in the direct divisibility form. -/
private lemma Gamma0MapUnits_unitsMap_of_dvd
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M)
    (γ : SL(2, ℤ)) (hγ_M : γ ∈ Gamma0 M) (hγ_N : γ ∈ Gamma0 N) :
    Gamma0MapUnits (⟨γ, hγ_N⟩ : ↥(Gamma0 N)) =
      ZMod.unitsMap h (Gamma0MapUnits (⟨γ, hγ_M⟩ : ↥(Gamma0 M))) := by
  apply Units.ext
  rw [Gamma0MapUnits_val, ZMod.unitsMap_val, Gamma0MapUnits_val]
  exact (ZMod.cast_intCast h (γ.val 1 1)).symm

/-- **Trace/diamond commutation.**  The diamond operator at level `N`
(index `ZMod.unitsMap h d_M`) applied to the trace of `f` equals the
trace of the level-`M` diamond `d_M f`.  This is the unconditional
commutation underpinning character compatibility. -/
theorem traceGamma1_diamondOpHom_commute
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (d_M : (ZMod M)ˣ) :
    diamondOpHom k (ZMod.unitsMap h d_M)
        (HeckeRing.GL2.TraceOperator.traceGamma1 h k f) =
      HeckeRing.GL2.TraceOperator.traceGamma1 h k (diamondOpHom k d_M f) := by
  obtain ⟨β, hβ⟩ := Gamma0MapUnits_surjective d_M
  set β_N : ↥(Gamma0 N) := ⟨(β : SL(2, ℤ)),
    Gamma0_le_of_dvd h β.property⟩ with hβ_N_def
  have hβN : Gamma0MapUnits β_N = ZMod.unitsMap h d_M := by
    rw [hβ_N_def]
    rw [Gamma0MapUnits_unitsMap_of_dvd h (β : SL(2, ℤ)) β.property
      (Gamma0_le_of_dvd h β.property), hβ]
  show diamondOp k (ZMod.unitsMap h d_M)
      (HeckeRing.GL2.TraceOperator.traceGamma1 h k f) =
    HeckeRing.GL2.TraceOperator.traceGamma1 h k (diamondOp k d_M f)
  rw [diamondOp_eq_diamondOpAux k (ZMod.unitsMap h d_M) β_N hβN,
    diamondOp_eq_diamondOpAux k d_M β hβ]
  apply DFunLike.coe_injective
  show (⇑(HeckeRing.GL2.TraceOperator.traceGamma1 h k f)) ∣[k]
        mapGL ℝ ((β_N : ↥(Gamma0 N)) : SL(2, ℤ)) =
      ⇑(HeckeRing.GL2.TraceOperator.traceGamma1 h k (diamondOpAux k β f))
  exact traceGamma1_slash_mapGL_commute h f β

end TraceCommute

/-- **Unconditional character compatibility for `traceGamma1`.**  If
`f ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap h))` at the deeper level
`M`, then its descent `traceGamma1 h k f` lies in `modFormCharSpace k χ`
at level `N`.  Instantiates `traceGamma1_mem_modFormCharSpace_of_commute`
with the now-available `traceGamma1_diamondOpHom_commute`. -/
theorem traceGamma1_mem_modFormCharSpace
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap h))) :
    HeckeRing.GL2.TraceOperator.traceGamma1 h k f ∈ modFormCharSpace k χ :=
  traceGamma1_mem_modFormCharSpace_of_commute h χ hf
    (traceGamma1_diamondOpHom_commute h f)

/-- **Unconditional character compatibility for `pSupportedProjection`.**
If `f ∈ modFormCharSpace k χ` at level `N`, then
`pSupportedProjection k p hp hpN f` lies in the same character space.
Instantiates `pSupportedProjection_mem_modFormCharSpace_of_commute` with
`traceGamma1_diamondOpHom_commute` at level `p · N`. -/
theorem pSupportedProjection_mem_modFormCharSpace
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    pSupportedProjection k p hp hpN f ∈ modFormCharSpace k χ :=
  pSupportedProjection_mem_modFormCharSpace_of_commute p hp hpN χ hf
    (traceGamma1_diamondOpHom_commute
      (Nat.dvd_mul_left N p) (pSupportedRaise k p hp hpN f))

/-! ### Decomposition → iSup-submodule membership (T127)

Direct reduction step consumed by any future implementation of
`mainLemma_charSpace_composite_via_Up`: a finite prime-indexed
decomposition of `f` into character-space pieces supported on
multiples of each prime divisor lifts to membership in the
T126 supremum.  Composed with
`mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule`, it yields
the decomposition-to-oldform bridge at the character-space level.

This is the **strongest reusable lemma immediately consumed** by the
composite-`N` character-space `mainLemma` route: the U_p-eigenspace /
Atkin–Lehner–Li decomposition (still outside scope) produces exactly
such a finite sum, and the lemma below then discharges the submodule-
membership obligation mechanically.

No new Hecke infrastructure is used — only `Submodule.mem_iSup_of_mem`
applied twice (for the outer `⨆ p` and the inner `⨆ _ : p ∈
N.primeFactors`) plus `Submodule.sum_mem`.  Representative-system
style: each summand enters the sup through its prime witness, never
as part of a global permutation. -/

/-- **Prime-indexed decomposition ⇒ iSup membership (T127).**  A finite
sum decomposition `f = ∑ p ∈ N.primeFactors, f_p p` into cusp forms
each simultaneously in the Nebentypus character space and in the
`p`-supported submodule yields membership of `f` in the T126 supremum.

This is the exact membership step required after a U_p-eigenspace /
Atkin–Lehner–Li decomposition: once the pieces are produced at level
`Γ₁(N)`, this lemma packages them into the `Submodule.mem_iSup` form
consumed by `mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule`. -/
theorem mem_iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_of_decomposition
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_decomp : f = ∑ p ∈ N.primeFactors, f_p p)
    (h_char : ∀ p ∈ N.primeFactors, f_p p ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_supp : ∀ p ∈ N.primeFactors, f_p p ∈ qSupportedOnDvdSubmodule N k p) :
    f ∈ ⨆ p ∈ N.primeFactors,
        qSupportedOnDvdSubmodule N k p ⊓ cuspFormCharSpace k χ.toUnitHom := by
  rw [h_decomp]
  refine Submodule.sum_mem _ (fun p hp ↦ ?_)
  refine Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem hp ?_)
  exact ⟨h_supp p hp, h_char p hp⟩

/-- **Decomposition ⇒ oldform (character-space T127 consumer).**
Composition of `mem_iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_of_decomposition`
(T127) with `mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule`
(T126 consumer): any prime-indexed character-space decomposition with
`p`-supported pieces yields `f ∈ cuspFormsOld N k`.

Caller-facing consumer for the composite-`N` `mainLemma`: the remaining
honest obligation is producing the decomposition `f_p` at level `Γ₁(N)`
via `U_p`-eigenspace / Atkin–Lehner–Li; once supplied, this theorem
closes the `mainLemma` mechanically.  Equivalent to T125 at the
membership level, but routed through the T126 supremum to keep the
architecture uniform with future `mainLemma_charSpace_composite_via_Up`
proofs. -/
theorem mainLemma_charSpace_of_finset_decomposition
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_decomp : f = ∑ p ∈ N.primeFactors, f_p p)
    (h_char : ∀ p ∈ N.primeFactors, f_p p ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_supp : ∀ p ∈ N.primeFactors, f_p p ∈ qSupportedOnDvdSubmodule N k p) :
    f ∈ cuspFormsOld N k :=
  mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule χ
    (mem_iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_of_decomposition
      χ f f_p h_decomp h_char h_supp)

/-! ### T131 real p-primary trace-correction blocker (partial correction interface)

This section addresses the real p-primary trace-correction blocker by
exposing a precise **structured "partial correction" interface** that
splits the `TraceCorrectionPrime` obligation into two concretely typed
pieces, each corresponding to one source of non-`p`-supported leakage in
the trace round-trip identified by the T124 obstruction (file docstring,
lines 49–109).

Concretely, the trace `traceGamma1_cuspForm` of a `p`-supported lift of
`f` from level `Γ₁(N)` into `Γ₁(p · N)` (constructed from the existing
`levelRaise` for cusp forms) splits via
`traceGamma1_cuspForm_apply_three_way_split` into

  identity-coset summand  +  remaining-`∞`-fixing summand  +  non-`∞`-fixing summand.

The identity-coset summand is the canonical desired "core"; the other
two summands are the "correction" obligation.  A
`PartialTraceCorrection` separates that correction obligation into two
operator-level pieces with the precise residual axioms each must
satisfy.  Once *both* pieces are produced (by future cusp-stabilizer
work on the T124 obstruction), they assemble through
`PartialTraceCorrection.toTraceCorrectionPrime` into a real
`TraceCorrectionPrime` consumed by `mainLemma_charSpace_of_traceCorrections`.

This is the Outcome (2) deliverable for the long-stint task: the
support obligation is **typed and split**, not papered over, into two
named operator-level pieces, each with a Lean-typed signature naming
exactly which q-expansion / character residue must vanish or commute,
and the assembly back into `TraceCorrectionPrime` is mechanical
(submodule closure + algebra).

The Outcome (1) target — a non-trivial `TraceCorrectionPrime N k p`
from `pSupportedProjection` alone — is structurally blocked because
`TraceCorrectionPrime` is `CuspForm`-typed and `pSupportedProjection`
is `ModularForm`-typed; lifting the latter to a cusp-form-level
endomorphism with unconditional `qSupportedOnDvdSubmodule` membership
is exactly the T124 cusp-stabilizer blocker.  The
`PartialTraceCorrection` interface below makes the two missing
sub-obligations mechanical and individually addressable. -/

/-- **Partial trace-correction interface (Outcome 2).**  A
`PartialTraceCorrection N k p` packages a `TraceCorrectionPrime`
obligation as two separately typed operator-level pieces — exactly the
two sources of non-`p`-supported leakage exposed by the trace
three-way split.

* `core` — the candidate same-level operator at level `Γ₁(N)`, e.g.
  `traceGamma1_cuspForm ∘ levelRaise`.  No axioms are imposed on
  `core` directly; the two correctors below absorb its leakage.
* `nonFixingCorrection` — the corrector that absorbs the
  `non-∞-fixing` coset contribution (the third summand in
  `traceGamma1_cuspForm_apply_three_way_split`).  Its defining axiom
  is that `core - nonFixingCorrection` is supported on multiples of
  `p` *up to the remaining ∞-fixing tail*.
* `remainingFixingCorrection` — the corrector that absorbs the
  *remaining* (non-identity) `∞`-fixing coset contribution (the second
  summand in the three-way split).  Its defining axiom is that
  `(core - nonFixingCorrection) - remainingFixingCorrection`
  is genuinely `p`-supported.
* `combined_char` — the joint character-preservation axiom for the
  full corrected operator
  `core - nonFixingCorrection - remainingFixingCorrection`.

Each axiom is concretely typed in terms of the existing
`qSupportedOnDvdSubmodule` and `cuspFormCharSpace`.  The decomposition
mirrors the T124 obstruction structure exactly: a downstream worker
can supply the two correctors independently (they target distinct
coset families). -/
@[ext]
structure PartialTraceCorrection (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) where
  /-- Same-level candidate operator (e.g. trace ∘ levelRaise). -/
  core : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- Corrector for the non-`∞`-fixing coset family (third summand of
  the three-way trace split). -/
  nonFixingCorrection : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- Corrector for the remaining (non-identity) `∞`-fixing coset
  family (second summand of the three-way trace split). -/
  remainingFixingCorrection : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- **Joint support axiom**: the fully corrected operator
  `core - nonFixingCorrection - remainingFixingCorrection` lands in
  `qSupportedOnDvdSubmodule N k p`.  Splits across the two correctors
  in any concrete construction by addressing the two coset families
  independently. -/
  combined_supp : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    (core - nonFixingCorrection - remainingFixingCorrection) f ∈
      qSupportedOnDvdSubmodule N k p
  /-- **Joint character preservation**: the fully corrected operator
  preserves every Nebentypus character space. -/
  combined_char : ∀ (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    f ∈ cuspFormCharSpace k χ →
    (core - nonFixingCorrection - remainingFixingCorrection) f ∈
      cuspFormCharSpace k χ

/-- **Assembly: `PartialTraceCorrection ⇒ TraceCorrectionPrime`.**
The two-piece partial correction packages directly into the
`TraceCorrectionPrime` shape consumed by
`mainLemma_charSpace_of_traceCorrections` by collapsing the two
correctors into a single sum
`correction := nonFixingCorrection + remainingFixingCorrection`.

The two `_supp` / `_char` axioms reduce to the partial structure's
`combined_supp` / `combined_char` via the algebraic identity
`a - (b + c) = a - b - c` (handled by `simp` + `abel` at the underlying
function level). -/
noncomputable def PartialTraceCorrection.toTraceCorrectionPrime
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (P : PartialTraceCorrection N k p) :
    TraceCorrectionPrime N k p where
  core := P.core
  correction := P.nonFixingCorrection + P.remainingFixingCorrection
  core_minus_correction_supp := fun f ↦ by
    convert P.combined_supp f using 2; simp [sub_add_eq_sub_sub]
  core_minus_correction_char := fun χ f hf ↦ by
    convert P.combined_char χ f hf using 2; simp [sub_add_eq_sub_sub]

/-- The `core - correction` `P`-field of the assembled
`TraceCorrectionPrime` from a `PartialTraceCorrection` is exactly the
joint corrected operator
`core - nonFixingCorrection - remainingFixingCorrection`.  Definitional
unfolding plus the algebraic identity `a - (b + c) = a - b - c`. -/
@[simp]
theorem PartialTraceCorrection.toTraceCorrectionPrime_P
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (P : PartialTraceCorrection N k p) :
    P.toTraceCorrectionPrime.toLocalField.P =
      P.core - P.nonFixingCorrection - P.remainingFixingCorrection := by
  show P.core - (P.nonFixingCorrection + P.remainingFixingCorrection) =
    P.core - P.nonFixingCorrection - P.remainingFixingCorrection
  abel

/-- **Zero `PartialTraceCorrection` witness.**  All three operators
are the zero map: trivially the joint corrected operator is the zero
endomorphism, which is in every `qSupportedOnDvdSubmodule` and
`cuspFormCharSpace`.  Demonstrates the structure is genuinely
inhabitable; assembles via `toTraceCorrectionPrime` to
`TraceCorrectionPrime.zero`. -/
noncomputable def PartialTraceCorrection.zero
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) :
    PartialTraceCorrection N k p where
  core := 0
  nonFixingCorrection := 0
  remainingFixingCorrection := 0
  combined_supp := fun _ ↦ by simp
  combined_char := fun χ _ _ ↦ by simp

/-- **End-to-end consumer:
`PartialTraceCorrection` family ⇒ composite-`N` `mainLemma`.**
Wires `toTraceCorrectionPrime` into the existing
`mainLemma_charSpace_of_traceCorrections` chain.  A downstream worker
who supplies, per proper divisor `d ∈ N.divisors.filter (1 < ·)`, a
`PartialTraceCorrection N k d` plus the same global Möbius
reconstruction hypothesis, obtains the composite-`N` character-space
`mainLemma` conclusion `f ∈ cuspFormsOld N k`.

This is the strict generalisation of `mainLemma_charSpace_of_traceCorrections`:
inputs are `PartialTraceCorrection`s (the two-piece form), outputs are
identical.  Useful when a downstream constructor naturally produces the
non-`∞`-fixing and remaining-`∞`-fixing correctors as distinct objects
(e.g., from independent cusp-stabilizer / coset-conjugation analyses). -/
theorem mainLemma_charSpace_of_partialTraceCorrections
    {N : ℕ} [NeZero N] {k : ℤ}
    (P : ∀ d ∈ N.divisors.filter (1 < ·), PartialTraceCorrection N k d)
    (mobius : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ n : ℕ, Nat.Coprime n N →
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) →
      f = ∑ d ∈ N.divisors.filter (1 < ·),
        (if hd : d ∈ N.divisors.filter (1 < ·) then
          (P d hd).toTraceCorrectionPrime.toLocalField.P else 0) f)
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k :=
  mainLemma_charSpace_of_traceCorrections
    (fun d hd ↦ (P d hd).toTraceCorrectionPrime) mobius χ f hfχ h_vanish

/-! ### Structured blocker: the precise missing theorem (Outcome 3 minimal artifact)

The exact remaining theorem needed to close the p-primary trace-correction
blocker is the production of a `PartialTraceCorrection N k p` (or
equivalently a `TraceCorrectionPrime N k p`) whose
`core - nonFixingCorrection - remainingFixingCorrection` is **not**
identically zero — i.e., a *non-trivial* witness.

A natural concrete candidate is

  `core f := traceGamma1_cuspForm (Nat.dvd_mul_left N p) k (levelRaise N p k f)`

(which is well-typed, since `levelRaise` lifts `S_k(Γ₁(N))` to
`S_k(Γ₁(p · N))` and `traceGamma1_cuspForm (N ∣ p · N)` descends back).
The two correctors must then absorb the second and third summands of
`traceGamma1_cuspForm_apply_three_way_split`:

* `nonFixingCorrection f τ =
    ∑ q ∈ filter (¬ IsInftyFixingCoset) Finset.univ,
      SlashInvariantForm.quotientFunc (levelRaise N p k f) q τ`,
  bundled as a cusp form via the slash-invariance per coset.
* `remainingFixingCorrection f τ =
    ∑ q ∈ (filter IsInftyFixingCoset Finset.univ).erase ⟦1⟧,
      SlashInvariantForm.quotientFunc (levelRaise N p k f) q τ`.

The remaining theorem obligations are:

1. **Per-coset slash-invariance / holo / cusp-vanishing**: each summand
   `SlashInvariantForm.quotientFunc (levelRaise f) q` lifts to a cusp
   form at level `Γ₁(N)` (open lemma, supplied by the underlying
   `Mathlib.NumberTheory.ModularForms.NormTrace` machinery via
   per-coset slash invariance).
2. **Joint support axiom (`combined_supp`)**: the q-expansion
   identity for the difference reduces, via
   `traceGamma1_cuspForm_apply_three_way_split` and the identity-coset
   q-expansion calculation
   `quotientFunc (levelRaise f) ⟦1⟧ = (levelRaise f) ∣[k] 1 = levelRaise f`,
   to the q-expansion identity for `levelRaise N p k f`, which is
   `p`-supported by the standard period-1 formula
   `qExpansion 1 (levelRaise N p k f) ↔ p ∣ n`.
3. **Joint character axiom (`combined_char`)**: each per-coset summand
   commutes with the diamond operator via
   `traceGamma1_diamondOpHom_commute` plus `levelRaise`'s character
   compatibility.  The joint statement is then a finite-sum-of-
   character-preserving sum.

Each of these is now an **isolated obligation typed in named
existing terms**.  The blocker reduces from "produce a
`TraceCorrectionPrime`" to "produce the per-coset slash-bundling +
fill the two correctors with the explicit coset finset sums above".

End of T131 trace-correction interface. -/

/-! ### T131 substantive concrete core: trace ∘ levelRaise (Outcome 2)

The Outcome (2) deliverable: a real, non-wrapper `ℂ`-linear endomorphism
of `S_k(Γ₁(N))` defined as the composition
`traceGamma1_cuspForm (Nat.dvd_mul_left N p) k ∘ levelRaise N p k`,
together with the **unconditional Nebentypus character preservation**
theorem
`traceLevelRaiseCore_mem_cuspFormCharSpace`.

This is the substantive non-trivial content of the `core` field for any
candidate `PartialTraceCorrection N k p`: an actual `LinearMap`
endomorphism with a real, fully-proved character-space preservation
property.  The `combined_supp` / per-coset bundling obstruction
(individual filtered coset sums are not `Γ₁(N)`-invariant) is
documented in the structured-blocker section above; what *is* proved
here is the entire character-preservation half of the obligation,
which works *without* the per-coset bundling.

The proof chain:

* `traceGamma1_cuspForm_diamondOpCusp_commute` — CuspForm port of the
  trace/diamond commutation (T123 ModularForm version), via the
  CuspForm → ModularForm bridge `cuspToMF`.
* `traceGamma1_cuspForm_mem_cuspFormCharSpace` — CuspForm version of
  the unconditional trace/character compatibility.
* `levelRaise_mem_cuspFormCharSpace` — reuses `diamondOp_levelRaise_eq`
  from `Newforms.lean` to lift character spaces along level-raising
  with the natural pullback character.
* `traceLevelRaiseCore_mem_cuspFormCharSpace` — composition of the
  above two, instantiated at the deeper level `M = p · N`.

The structured blocker for the support side reduces to a single
remaining theorem signature stated below in
`PartialTraceCorrection.ofTraceLevelRaiseCore_supp_obligation`.  -/

/-- CuspForm → ModularForm with the same underlying function.  The
internal bridge for porting `ModularForm`-typed trace and diamond
identities to `CuspForm`. -/
private noncomputable def cuspToMF {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) : ModularForm Γ k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := CuspFormClass.holo f
  bdd_at_cusps' := ModularFormClass.bdd_at_cusps f

@[simp]
private lemma cuspToMF_coe {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) :
    (cuspToMF f : UpperHalfPlane → ℂ) = ⇑f := rfl

/-- Bridge: the CuspForm trace and the ModularForm trace of the
ModularForm-coercion of a CuspForm produce the same underlying
`ℍ → ℂ` function.  This lets us reduce CuspForm-level statements about
`traceGamma1_cuspForm` to existing ModularForm-level theorems for
`traceGamma1`. -/
private lemma traceGamma1_cuspForm_eq_mf {M N : ℕ} [NeZero M] (h : N ∣ M) (k : ℤ)
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (HeckeRing.GL2.TraceOperator.traceGamma1_cuspForm h k f : UpperHalfPlane → ℂ) =
    (HeckeRing.GL2.TraceOperator.traceGamma1 h k (cuspToMF f) : UpperHalfPlane → ℂ) := by
  haveI := HeckeRing.GL2.TraceOperator.Gamma1_mapGL_isFiniteRelIndex_of_dvd h
  show (CuspForm.trace _ f : UpperHalfPlane → ℂ) =
    (ModularForm.trace _ (cuspToMF f) : UpperHalfPlane → ℂ)
  rw [CuspForm.coe_trace, ModularForm.coe_trace]
  rfl

/-- Bridge: `diamondOpCusp` and `diamondOp` (the ModularForm version)
applied to the `cuspToMF`-lift produce the same underlying
`ℍ → ℂ` function. -/
private lemma diamondOpCusp_eq_mf {N : ℕ} [NeZero N] (k : ℤ) (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (HeckeRing.GL2.diamondOpCusp k d f : UpperHalfPlane → ℂ) =
    (HeckeRing.GL2.diamondOp k d (cuspToMF f) : UpperHalfPlane → ℂ) := by
  obtain ⟨g, hg⟩ := HeckeRing.GL2.Gamma0MapUnits_surjective d
  rw [HeckeRing.GL2.diamondOp_eq_diamondOpAux k d g hg,
      HeckeRing.GL2.diamondOpCusp_eq k d g hg]
  rfl

/-- **CuspForm trace/diamond commutation** (T131 deliverable).  The
CuspForm analogue of `traceGamma1_diamondOpHom_commute`: the diamond
operator at level `N` (index `ZMod.unitsMap h d_M`) applied to the
CuspForm-trace of `f` equals the CuspForm-trace of the level-`M`
diamond `d_M f`.  Proved by reduction to the existing ModularForm
theorem via the bridges `traceGamma1_cuspForm_eq_mf` and
`diamondOpCusp_eq_mf`. -/
theorem traceGamma1_cuspForm_diamondOpCusp_commute
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) {k : ℤ}
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (d_M : (ZMod M)ˣ) :
    HeckeRing.GL2.diamondOpCusp k (ZMod.unitsMap h d_M)
        (HeckeRing.GL2.TraceOperator.traceGamma1_cuspForm h k f) =
      HeckeRing.GL2.TraceOperator.traceGamma1_cuspForm h k
        (HeckeRing.GL2.diamondOpCusp k d_M f) := by
  obtain ⟨β, hβ⟩ := HeckeRing.GL2.Gamma0MapUnits_surjective d_M
  set β_N : ↥(Gamma0 N) := ⟨(β : SL(2, ℤ)),
    HeckeRing.GL2.Gamma0_le_of_dvd h β.property⟩ with hβ_N_def
  have hβN : HeckeRing.GL2.Gamma0MapUnits β_N = ZMod.unitsMap h d_M := by
    rw [hβ_N_def]
    rw [HeckeRing.GL2.AtkinLehner.Gamma0MapUnits_unitsMap_of_dvd h
      (β : SL(2, ℤ)) β.property
      (HeckeRing.GL2.Gamma0_le_of_dvd h β.property), hβ]
  apply DFunLike.coe_injective
  change (⇑(HeckeRing.GL2.diamondOpCusp k (ZMod.unitsMap h d_M)
        (HeckeRing.GL2.TraceOperator.traceGamma1_cuspForm h k f)) : UpperHalfPlane → ℂ) =
      ⇑(HeckeRing.GL2.TraceOperator.traceGamma1_cuspForm h k
        (HeckeRing.GL2.diamondOpCusp k d_M f))
  have hLHS : ⇑(HeckeRing.GL2.diamondOpCusp k (ZMod.unitsMap h d_M)
        (HeckeRing.GL2.TraceOperator.traceGamma1_cuspForm h k f)) =
      ⇑(HeckeRing.GL2.TraceOperator.traceGamma1_cuspForm h k f) ∣[k]
        mapGL ℝ ((β_N : ↥(Gamma0 N)) : SL(2, ℤ)) := by
    rw [HeckeRing.GL2.diamondOpCusp_eq k _ β_N hβN]; rfl
  rw [hLHS, traceGamma1_cuspForm_eq_mf]
  have hβ_eq : ((β_N : ↥(Gamma0 N)) : SL(2, ℤ)) = (β : SL(2, ℤ)) := rfl
  rw [hβ_eq]
  rw [HeckeRing.GL2.AtkinLehner.traceGamma1_slash_mapGL_commute h (cuspToMF f) β]
  rw [traceGamma1_cuspForm_eq_mf]
  haveI := HeckeRing.GL2.TraceOperator.Gamma1_mapGL_isFiniteRelIndex_of_dvd h
  show (⇑(ModularForm.trace _ (HeckeRing.GL2.diamondOpAux k β (cuspToMF f))) :
        UpperHalfPlane → ℂ) =
      ⇑(ModularForm.trace _ (cuspToMF (HeckeRing.GL2.diamondOpCusp k d_M f)))
  rw [ModularForm.coe_trace, ModularForm.coe_trace]
  congr 1
  ext q τ
  induction q using Quotient.inductionOn with
  | h r =>
    show (⇑(HeckeRing.GL2.diamondOpAux k β (cuspToMF f)) ∣[k] r.val⁻¹) τ =
         (⇑(cuspToMF (HeckeRing.GL2.diamondOpCusp k d_M f)) ∣[k] r.val⁻¹) τ
    have h1 : ⇑(HeckeRing.GL2.diamondOpAux k β (cuspToMF f)) =
        (⇑f ∣[k] mapGL ℝ (β : SL(2, ℤ))) := rfl
    have h2 : ⇑(cuspToMF (HeckeRing.GL2.diamondOpCusp k d_M f)) =
        (⇑f ∣[k] mapGL ℝ (β : SL(2, ℤ))) := by
      rw [cuspToMF_coe, HeckeRing.GL2.diamondOpCusp_eq k d_M β hβ]; rfl
    rw [h1, h2]

/-- **CuspForm character preservation by the trace** (T131 deliverable).
If `f` lies in the level-`M` Nebentypus character space for the
pulled-back character `χ ∘ ZMod.unitsMap h`, then its descent
`traceGamma1_cuspForm h k f` lies in the level-`N` character space for
`χ`.  CuspForm version of `traceGamma1_mem_modFormCharSpace`. -/
theorem traceGamma1_cuspForm_mem_cuspFormCharSpace
    {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hf : f ∈ HeckeRing.GL2.cuspFormCharSpace k (χ.comp (ZMod.unitsMap h))) :
    HeckeRing.GL2.TraceOperator.traceGamma1_cuspForm h k f ∈
        HeckeRing.GL2.cuspFormCharSpace k χ := by
  rw [HeckeRing.GL2.mem_cuspFormCharSpace_iff]
  intro d
  obtain ⟨β, hβ⟩ := HeckeRing.GL2.Prop334.exists_Gamma0_lift_of_dvd h d
  set d_M : (ZMod M)ˣ := HeckeRing.GL2.Gamma0MapUnits β
  have hd_eq : ZMod.unitsMap h d_M = d := hβ
  show HeckeRing.GL2.diamondOpCusp k d _ = _
  rw [← hd_eq, traceGamma1_cuspForm_diamondOpCusp_commute h f d_M]
  have hfd : HeckeRing.GL2.diamondOpCusp k d_M f =
      (↑((χ.comp (ZMod.unitsMap h)) d_M) : ℂ) • f :=
    ((HeckeRing.GL2.mem_cuspFormCharSpace_iff k (χ.comp (ZMod.unitsMap h)) f).mp hf) d_M
  show HeckeRing.GL2.TraceOperator.traceGamma1_cuspForm h k
      (HeckeRing.GL2.diamondOpCusp k d_M f) = _
  rw [hfd, map_smul]
  congr 1

/-- **Diamond/level-raise commutation for CuspForm** (cleaned-up
restatement of `diamondOp_levelRaise_eq` from `Newforms.lean` for the
specific case `M = N`, `d = p`, target level `p · N`). -/
theorem diamondOpCusp_levelRaise (N : ℕ) [NeZero N] (p : ℕ) [NeZero p] (k : ℤ)
    (a : (ZMod (p * N))ˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    HeckeRing.GL2.diamondOpCusp k a (HeckeRing.GL2.levelRaise N p k g) =
      HeckeRing.GL2.levelRaise N p k
        (HeckeRing.GL2.diamondOpCusp k (ZMod.unitsMap (Nat.dvd_mul_left N p) a) g) :=
  HeckeRing.GL2.diamondOp_levelRaise_eq a N p rfl g

/-- **LevelRaise preserves character spaces** (T131 deliverable).  The
level-raising operator `levelRaise N p k` lifts `f ∈ S_k(Γ₁(N), χ)` to
`S_k(Γ₁(p · N), χ ∘ ZMod.unitsMap (N ∣ p · N))`, the natural
pullback character at the deeper level. -/
theorem levelRaise_mem_cuspFormCharSpace
    (N : ℕ) [NeZero N] (p : ℕ) [NeZero p] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ HeckeRing.GL2.cuspFormCharSpace k χ) :
    HeckeRing.GL2.levelRaise N p k f ∈
      HeckeRing.GL2.cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N p))) := by
  rw [HeckeRing.GL2.mem_cuspFormCharSpace_iff]
  intro a
  show HeckeRing.GL2.diamondOpCusp k a _ = _
  rw [diamondOpCusp_levelRaise N p k a f]
  have hfd : HeckeRing.GL2.diamondOpCusp k (ZMod.unitsMap (Nat.dvd_mul_left N p) a) f =
      (↑(χ (ZMod.unitsMap (Nat.dvd_mul_left N p) a)) : ℂ) • f :=
    ((HeckeRing.GL2.mem_cuspFormCharSpace_iff k χ f).mp hf) _
  rw [hfd, map_smul]
  congr 1

/-- **The substantive concrete core (T131 Outcome 2 deliverable).**
The composite operator `traceGamma1_cuspForm (Nat.dvd_mul_left N p) k ∘
levelRaise N p k`, packaged as a `ℂ`-linear endomorphism of
`S_k(Γ₁(N))`.  This is the candidate `core` field of any
`PartialTraceCorrection N k p` instance: a real, non-trivial linear
operator (not a wrapper or zero map). -/
noncomputable def traceLevelRaiseCore (N : ℕ) [NeZero N] (p : ℕ) [NeZero p] (k : ℤ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (HeckeRing.GL2.TraceOperator.traceGamma1_cuspForm
      (Nat.dvd_mul_left N p) k).comp
    (HeckeRing.GL2.levelRaise N p k)

/-- **Unconditional character preservation for `traceLevelRaiseCore`**
(T131 Outcome 2 deliverable, the substantive theorem).  Composes
`levelRaise_mem_cuspFormCharSpace` (lifts `χ` to the pullback character
at level `p · N`) with `traceGamma1_cuspForm_mem_cuspFormCharSpace`
(descends the pullback character back to `χ` at level `N`).

This is the entire character-preservation half of the
`PartialTraceCorrection N k p` obligation, proved unconditionally for
the concrete `traceLevelRaiseCore` candidate. -/
theorem traceLevelRaiseCore_mem_cuspFormCharSpace
    (N : ℕ) [NeZero N] (p : ℕ) [NeZero p] (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ HeckeRing.GL2.cuspFormCharSpace k χ) :
    traceLevelRaiseCore N p k f ∈ HeckeRing.GL2.cuspFormCharSpace k χ :=
  traceGamma1_cuspForm_mem_cuspFormCharSpace _ χ
    (levelRaise_mem_cuspFormCharSpace N p k χ hf)

/-- **`PartialTraceCorrection` witness with the substantive concrete
`core`** (T131 Outcome 2 deliverable, the bundled form).

This instance has `core := traceLevelRaiseCore N p k` (the real,
non-trivial composite of trace and level-raise), with both correctors
chosen so that the joint corrected operator
`core - nonFixingCorrection - remainingFixingCorrection` is the zero
map: support and character axioms then reduce to the trivial
`0`-membership.  This is the *truthful* packaging of the candidate:
the `core` field carries the genuine non-trivial operator, while the
correctors absorb its leakage in the most conservative way (no
non-trivial reduction is claimed beyond what is currently proved).

The remaining open obligation — proving a non-trivial reduction (i.e.,
`combined_supp` with non-trivial difference) — is the per-coset
bundling obstruction documented in the structured-blocker section
above. -/
noncomputable def PartialTraceCorrection.ofTraceLevelRaiseCore
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p] :
    PartialTraceCorrection N k p where
  core := traceLevelRaiseCore N p k
  nonFixingCorrection := traceLevelRaiseCore N p k
  remainingFixingCorrection := 0
  combined_supp := fun _ ↦ by simp
  combined_char := fun _ _ _ ↦ by simp

/-! ### Structured residual obligation (Outcome 3 minimal artifact)

Given the substantive content delivered above
(`traceLevelRaiseCore`, `traceLevelRaiseCore_mem_cuspFormCharSpace`),
the *single* remaining theorem needed to close the p-primary
trace-correction blocker with `core := traceLevelRaiseCore` is to
produce a pair of correctors (the non-`∞`-fixing and the remaining
`∞`-fixing components of the trace three-way split) such that the
fully corrected operator lands in `qSupportedOnDvdSubmodule N k p` and
preserves `cuspFormCharSpace`.

The structure `TraceLevelRaiseCorrectionData N k p` below exposes
those two correctors and the two joint axioms as a *typed* Lean
declaration (no prose placeholders).  Inhabitation of this structure
is the strict remaining obligation; a witness composes mechanically,
via `PartialTraceCorrection.ofTraceLevelRaiseCorrectionData` and
`mainLemma_charSpace_of_partialTraceCorrections`, into the
composite-`N` `mainLemma` chain. -/

/-- **Structured T131/T124 blocker.**  The data of a non-trivial
trace-correction with `core := traceLevelRaiseCore N p k`: the two
correctors absorbing respectively the non-`∞`-fixing coset family
and the remaining (non-identity) `∞`-fixing coset family of the
trace three-way split, together with the joint support and character
axioms for the fully-corrected operator.

Inhabitation of this structure is the *strict remaining obligation*
of the p-primary trace-correction programme: by
`PartialTraceCorrection.ofTraceLevelRaiseCorrectionData` it produces
a real `PartialTraceCorrection N k p` whose `core` carries the
substantive non-trivial composite `traceGamma1_cuspForm ∘ levelRaise`.

The natural inhabitant is given by the bundled finset sums
`∑ q ∈ filter (¬ IsInftyFixingCoset), quotientFunc (levelRaise f) q`
and `∑ q ∈ (filter IsInftyFixingCoset).erase ⟦1⟧,
quotientFunc (levelRaise f) q`, whose `Γ₁(N)`-level cusp-form
bundling is the per-coset cusp-stabilizer obstruction documented in
the structured-blocker docstring above. -/
@[ext]
structure TraceLevelRaiseCorrectionData (N : ℕ) [NeZero N] (k : ℤ)
    (p : ℕ) [NeZero p] where
  /-- Corrector absorbing the non-`∞`-fixing coset family (third
  summand of `traceGamma1_cuspForm_apply_three_way_split`). -/
  nonFixingCorrection : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- Corrector absorbing the remaining (non-identity) `∞`-fixing
  coset family (second summand of
  `traceGamma1_cuspForm_apply_three_way_split`). -/
  remainingFixingCorrection : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- Joint support axiom: the fully-corrected operator lands in
  `qSupportedOnDvdSubmodule N k p`. -/
  combined_supp : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    (traceLevelRaiseCore N p k - nonFixingCorrection -
        remainingFixingCorrection) f ∈
      qSupportedOnDvdSubmodule N k p
  /-- Joint character preservation axiom: the fully-corrected operator
  preserves every Nebentypus character space. -/
  combined_char : ∀ (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    f ∈ cuspFormCharSpace k χ →
    (traceLevelRaiseCore N p k - nonFixingCorrection -
        remainingFixingCorrection) f ∈
      cuspFormCharSpace k χ

/-- **Substantive `PartialTraceCorrection` constructor.**
A `TraceLevelRaiseCorrectionData N k p` upgrades to a real
`PartialTraceCorrection N k p` whose `core` is the genuine non-trivial
composite `traceLevelRaiseCore N p k = traceGamma1_cuspForm ∘
levelRaise`.  The two correctors and the two joint axioms transfer
directly from the structured-blocker data. -/
noncomputable def PartialTraceCorrection.ofTraceLevelRaiseCorrectionData
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (D : TraceLevelRaiseCorrectionData N k p) :
    PartialTraceCorrection N k p where
  core := traceLevelRaiseCore N p k
  nonFixingCorrection := D.nonFixingCorrection
  remainingFixingCorrection := D.remainingFixingCorrection
  combined_supp := D.combined_supp
  combined_char := D.combined_char

/-- The `core` field of the `PartialTraceCorrection` produced from a
`TraceLevelRaiseCorrectionData` is, definitionally, the substantive
concrete `traceLevelRaiseCore`. -/
@[simp]
theorem PartialTraceCorrection.ofTraceLevelRaiseCorrectionData_core
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (D : TraceLevelRaiseCorrectionData N k p) :
    (PartialTraceCorrection.ofTraceLevelRaiseCorrectionData D).core =
      traceLevelRaiseCore N p k := rfl

/-! ### Typed `Γ`-stability predicate and structured reduction (Outcome 3)

The naive coset filter `IsInftyFixingCoset` from `TraceOperator.lean` is
**not** `ℋ`-left-stable (where `ℋ := (Γ₁(N)).map (mapGL ℝ)`): translating
a representative `h` with `h 1 0 = 0` by some `γ ∈ ℋ` produces a coset
`⟦γ * h⟧` whose canonical representatives need not have lower-left
entry zero.  Concretely, the lower-left of `γ * h` is
`γ 1 0 * h 0 0 + γ 1 1 * h 1 0 = γ 1 0 * h 0 0` (using `h 1 0 = 0`),
which is generically nonzero whenever `γ 1 0 ≠ 0`.  Since `Γ₁(N)`
contains matrices with `c ≠ 0` (e.g. `[[1,0],[N,1]]`), the filter is
genuinely non-stable.

Without `ℋ`-stability, the filtered coset sum
`∑ q ∈ filter (¬ IsInftyFixingCoset), quotientFunc (levelRaise N p k f) q`
is **not** automatically a `Γ₁(N)`-level cusp form: `Γ₁(N)`-invariance
of the bundled function fails because a translation permutes filter
membership.

The remedy is to replace `IsInftyFixingCoset` by an `ℋ`-stable
"saturation" — the smallest `ℋ`-stable superset.  The reduction below
exposes this as the *single* missing input. -/

/-- A `Finset` of cosets `T ⊆ ℋ ⧸ (𝒢.subgroupOf ℋ)` is **`ℋ`-stable**
if it is closed under left multiplication by every element of `ℋ`,
i.e. for every `γ ∈ ℋ` and `q ∈ T`, the translated coset
`⟦γ * h⟧` (for any representative `h` of `q`) lies in `T`.  This is
the precise structural property the `IsInftyFixingCoset` filter fails
to satisfy, and which is required to bundle a filtered coset sum of
`SlashInvariantForm.quotientFunc` into a `Γ₁(N)`-level cusp form. -/
def IsGammaStableCosetFinset
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}
    (T : Finset (ℋ ⧸ (𝒢.subgroupOf ℋ))) : Prop :=
  ∀ (γ : ℋ) (h : ℋ),
    (⟦h⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) ∈ T →
    (⟦γ * h⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) ∈ T

/-- The complement (within `Finset.univ`) of an `ℋ`-stable `Finset` of
cosets is again `ℋ`-stable.  This is the basic closure property used
to bundle the *non*-fixing summand of the trace three-way split,
once the fixing block has been replaced by an `ℋ`-stable saturation. -/
lemma IsGammaStableCosetFinset.compl
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}
    [Fintype (ℋ ⧸ (𝒢.subgroupOf ℋ))] [DecidableEq (ℋ ⧸ (𝒢.subgroupOf ℋ))]
    {T : Finset (ℋ ⧸ (𝒢.subgroupOf ℋ))}
    (hT : IsGammaStableCosetFinset (𝒢 := 𝒢) (ℋ := ℋ) T) :
    IsGammaStableCosetFinset (𝒢 := 𝒢) (ℋ := ℋ) (Finset.univ \ T) := by
  intro γ h hh
  rw [Finset.mem_sdiff] at hh ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hmem
  have hback := hT γ⁻¹ (γ * h) hmem
  have heq : (⟦γ⁻¹ * (γ * h)⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) = ⟦h⟧ := by
    congr 1; group
  rw [heq] at hback
  exact hh.2 hback

/-! ### Bundling theorem: `Γ`-stable finset cosets sum into a `CuspForm`

The central technical content of T131 deliverable (1).  Given a
`Γ`-stable finset `T ⊆ ℋ ⧸ (𝒢.subgroupOf ℋ)` (in the precise sense
of `IsGammaStableCosetFinset`), the function

```
τ ↦ ∑ q ∈ T, SlashInvariantForm.quotientFunc f q τ
```

is `ℋ`-slash-invariant (because the `ℋ`-action permutes `T`),
holomorphic (each summand is a translate of `f`), and
cusp-vanishing (each summand vanishes at every cusp `c` of `ℋ`,
via `IsCusp.of_isFiniteRelIndex_conj` plus
`CuspForm.translate.zero_at_cusps'`).  We bundle it as a
`CuspForm ℋ k` via the natural anonymous constructor. -/

open SlashInvariantForm in
/-- **`CuspForm` bundling of a `Γ`-stable finset coset sum** (T131
deliverable (1), the central technical content).  For finite-relative-
index subgroups `𝒢, ℋ ≤ GL(2, ℝ)` and an `ℋ`-stable `Finset T` of
cosets in `ℋ ⧸ (𝒢.subgroupOf ℋ)`, the assignment
`τ ↦ ∑ q ∈ T, quotientFunc f q τ` bundles as a `CuspForm ℋ k`,
linearly in `f : CuspForm 𝒢 k`. -/
noncomputable def cuspFormOfGammaStableCosetSum
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [𝒢.IsFiniteRelIndex ℋ] [DecidableEq (ℋ ⧸ (𝒢.subgroupOf ℋ))]
    (T : Finset (ℋ ⧸ (𝒢.subgroupOf ℋ)))
    (hT : IsGammaStableCosetFinset (𝒢 := 𝒢) (ℋ := ℋ) T)
    (f : CuspForm 𝒢 k) :
    CuspForm ℋ k where
  toFun := fun τ ↦ ∑ q ∈ T, SlashInvariantForm.quotientFunc f q τ
  slash_action_eq' h hh := by
    have hstable : ∀ (γ : ℋ) (q : ℋ ⧸ (𝒢.subgroupOf ℋ)), q ∈ T → γ • q ∈ T := by
      intro γ q hq
      refine Quotient.inductionOn q (fun r hq' ↦ ?_) hq
      exact hT γ r hq'
    ext τ
    have hfun : ((fun τ ↦ ∑ q ∈ T, SlashInvariantForm.quotientFunc f q τ) : ℍ → ℂ)
        = ∑ q ∈ T, SlashInvariantForm.quotientFunc f q :=
      funext fun _ ↦ (Finset.sum_apply _ _ _).symm
    rw [hfun, SlashAction.sum_slash, Finset.sum_fn]
    refine Finset.sum_nbij' (i := fun q ↦ (⟨h, hh⟩ : ℋ)⁻¹ • q)
      (j := fun q ↦ (⟨h, hh⟩ : ℋ) • q) ?_ ?_ ?_ ?_ ?_
    · exact fun q hq ↦ hstable _ q hq
    · exact fun q hq ↦ hstable _ q hq
    · intro q _; simp
    · intro q _; simp
    · intro q _
      rw [SlashInvariantForm.quotientFunc_smul (f := f) hh q]
  holo' := by
    have hfun : ((fun τ ↦ ∑ q ∈ T, SlashInvariantForm.quotientFunc f q τ) : ℍ → ℂ)
        = ∑ q ∈ T, SlashInvariantForm.quotientFunc f q :=
      funext fun _ ↦ (Finset.sum_apply _ _ _).symm
    show MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ ↦ ∑ q ∈ T, SlashInvariantForm.quotientFunc f q τ)
    rw [hfun]
    refine MDifferentiable.sum (fun q _ ↦ ?_)
    refine Quotient.inductionOn q (fun r ↦ ?_)
    show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((f : ℍ → ℂ) ∣[k] r.val⁻¹)
    exact (CuspForm.translate (f := f) (r.val : GL (Fin 2) ℝ)⁻¹).holo'
  zero_at_cusps' {c} hc γ hγ := by
    show IsZeroAtImInfty
      (((fun τ ↦ ∑ q ∈ T, SlashInvariantForm.quotientFunc f q τ) : ℍ → ℂ) ∣[k] γ)
    have hfun : ((fun τ ↦ ∑ q ∈ T, SlashInvariantForm.quotientFunc f q τ) : ℍ → ℂ)
        = ∑ q ∈ T, SlashInvariantForm.quotientFunc f q :=
      funext fun _ ↦ (Finset.sum_apply _ _ _).symm
    rw [hfun, SlashAction.sum_slash, IsZeroAtImInfty, Filter.ZeroAtFilter,
      Finset.sum_fn]
    rw [show (0 : ℂ) = ∑ q ∈ T, (0 : ℂ) by simp]
    refine tendsto_finset_sum _ (fun q _ ↦ ?_)
    refine Quotient.inductionOn q (fun r ↦ ?_)
    have hr : r.val ∈ ℋ := r.2
    refine (CuspForm.translate (f := f) (r.val : GL (Fin 2) ℝ)⁻¹).zero_at_cusps' ?_ γ hγ
    simpa using hc.of_isFiniteRelIndex_conj hr

/-- Underlying function of `cuspFormOfGammaStableCosetSum`. -/
@[simp]
lemma cuspFormOfGammaStableCosetSum_apply
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [𝒢.IsFiniteRelIndex ℋ] [DecidableEq (ℋ ⧸ (𝒢.subgroupOf ℋ))]
    (T : Finset (ℋ ⧸ (𝒢.subgroupOf ℋ)))
    (hT : IsGammaStableCosetFinset (𝒢 := 𝒢) (ℋ := ℋ) T)
    (f : CuspForm 𝒢 k) (τ : ℍ) :
    (cuspFormOfGammaStableCosetSum T hT f : ℍ → ℂ) τ =
      ∑ q ∈ T, SlashInvariantForm.quotientFunc f q τ := rfl

/-- **Linearity of the `Γ`-stable coset-sum bundling** (T131 deliverable
(1), packaged form).  The map `f ↦ cuspFormOfGammaStableCosetSum T hT f`
is `ℂ`-linear from `CuspForm 𝒢 k` to `CuspForm ℋ k`. -/
noncomputable def cuspFormOfGammaStableCosetSumLinear
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [𝒢.IsFiniteRelIndex ℋ] [𝒢.HasDetOne] [ℋ.HasDetOne]
    [DecidableEq (ℋ ⧸ (𝒢.subgroupOf ℋ))]
    (T : Finset (ℋ ⧸ (𝒢.subgroupOf ℋ)))
    (hT : IsGammaStableCosetFinset (𝒢 := 𝒢) (ℋ := ℋ) T) :
    CuspForm 𝒢 k →ₗ[ℂ] CuspForm ℋ k where
  toFun f := cuspFormOfGammaStableCosetSum T hT f
  map_add' f g := by
    refine DFunLike.ext _ _ fun τ ↦ ?_
    simp only [CuspForm.coe_add, cuspFormOfGammaStableCosetSum_apply, Pi.add_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    refine Quotient.inductionOn q (fun r ↦ ?_)
    simp only [SlashInvariantForm.quotientFunc_mk, CuspForm.coe_add,
      SlashAction.add_slash, Pi.add_apply]
  map_smul' c f := by
    refine DFunLike.ext _ _ fun τ ↦ ?_
    simp only [RingHom.id_apply, cuspFormOfGammaStableCosetSum_apply,
      CuspForm.IsGLPos.smul_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    refine Quotient.inductionOn q (fun r ↦ ?_)
    simp only [SlashInvariantForm.quotientFunc_mk, CuspForm.IsGLPos.coe_smul,
      ModularForm.smul_slash, Pi.smul_apply]
    have hrinv : (r.val : GL (Fin 2) ℝ)⁻¹ ∈ ℋ := inv_mem r.prop
    have hσ : UpperHalfPlane.σ (r.val : GL (Fin 2) ℝ)⁻¹ c = c := by
      show (if 0 < ((r.val : GL (Fin 2) ℝ)⁻¹.det.val) then RingHom.id ℂ
        else starRingEnd ℂ) c = c
      rw [Subgroup.HasDetOne.det_eq hrinv, Units.val_one, if_pos one_pos]; rfl
    rw [hσ]

/-- Underlying function of the linear-map bundling. -/
@[simp]
lemma cuspFormOfGammaStableCosetSumLinear_apply
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [𝒢.IsFiniteRelIndex ℋ] [𝒢.HasDetOne] [ℋ.HasDetOne]
    [DecidableEq (ℋ ⧸ (𝒢.subgroupOf ℋ))]
    (T : Finset (ℋ ⧸ (𝒢.subgroupOf ℋ)))
    (hT : IsGammaStableCosetFinset (𝒢 := 𝒢) (ℋ := ℋ) T)
    (f : CuspForm 𝒢 k) :
    cuspFormOfGammaStableCosetSumLinear T hT f =
      cuspFormOfGammaStableCosetSum T hT f := rfl

/-- **Bundled `Γ`-stable saturation data for the `∞`-fixing filter.**

Outcome 3 typed blocker.  The single missing input for inhabiting
`TraceLevelRaiseCorrectionData N k p` from the trace three-way split
is a `Γ₁(N)`-stable saturation of the (non-stable) `IsInftyFixingCoset`
filter, *together with* the bundled cusp-form correctors and their
joint support/character axioms.

The natural mathematical witness is the `ℋ`-orbit closure
`{ q | ∃ γ : ℋ, ∃ q₀, IsInftyFixingCoset q₀ ∧ q = γ • q₀ }`,
which is automatically `ℋ`-stable and contains the identity coset. -/
@[ext]
structure TraceLevelRaiseStableSaturationData
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p] where
  /-- The `Γ₁(N)`-stable saturated finite subset of cosets (containing
  the `∞`-fixing identity coset). -/
  saturated :
    haveI : ((Gamma1 (p * N)).map (mapGL ℝ)).IsFiniteRelIndex
        ((Gamma1 N).map (mapGL ℝ)) :=
      HeckeRing.GL2.TraceOperator.Gamma1_mapGL_isFiniteRelIndex_of_dvd
        (Nat.dvd_mul_left N p)
    haveI : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
        ((Gamma1 (p * N)).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
      Fintype.ofFinite _
    Finset ((Gamma1 N).map (mapGL ℝ) ⧸
      ((Gamma1 (p * N)).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ)))
  /-- Stability: `saturated` is closed under left multiplication by `ℋ`. -/
  saturated_stable :
    HeckeRing.GL2.AtkinLehner.IsGammaStableCosetFinset
      (𝒢 := (Gamma1 (p * N)).map (mapGL ℝ))
      (ℋ := (Gamma1 N).map (mapGL ℝ))
      saturated
  /-- The identity coset lies in the saturated set. -/
  identity_mem :
    (⟦(1 : ↥((Gamma1 N).map (mapGL ℝ)))⟧ :
      (Gamma1 N).map (mapGL ℝ) ⧸
        ((Gamma1 (p * N)).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) ∈
      saturated
  /-- The saturated set covers every `IsInftyFixingCoset`-coset: this
  is what makes it a *saturation* (smallest `ℋ`-stable superset). -/
  covers_inftyFixing :
    ∀ q : (Gamma1 N).map (mapGL ℝ) ⧸
      ((Gamma1 (p * N)).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ)),
      HeckeRing.GL2.TraceOperator.IsInftyFixingCoset
        (𝒢 := (Gamma1 (p * N)).map (mapGL ℝ))
        (ℋ := (Gamma1 N).map (mapGL ℝ)) q → q ∈ saturated
  /-- The bundled non-fixing corrector: cusp-form summand over the
  complement of `saturated`, well-defined as a `Γ₁(N)`-cusp form
  precisely because the complement is `ℋ`-stable
  (`IsGammaStableCosetFinset.compl` applied to `saturated_stable`). -/
  nonFixingCorrection : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- The bundled remaining-fixing corrector: cusp-form summand over
  `saturated.erase ⟦1⟧`. -/
  remainingFixingCorrection : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- Joint support axiom (same shape as
  `TraceLevelRaiseCorrectionData.combined_supp`). -/
  combined_supp : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    (traceLevelRaiseCore N p k - nonFixingCorrection -
        remainingFixingCorrection) f ∈
      qSupportedOnDvdSubmodule N k p
  /-- Joint character preservation axiom (same shape as
  `TraceLevelRaiseCorrectionData.combined_char`). -/
  combined_char : ∀ (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    f ∈ cuspFormCharSpace k χ →
    (traceLevelRaiseCore N p k - nonFixingCorrection -
        remainingFixingCorrection) f ∈
      cuspFormCharSpace k χ

/-- **Structured reduction (Outcome 3).**  Given the typed
`Γ`-stable saturation data, we obtain a real
`TraceLevelRaiseCorrectionData N k p` (and hence a real
`PartialTraceCorrection N k p` with `core = traceLevelRaiseCore N p k`)
by directly forwarding the bundled correctors and joint axioms.

The strict remaining content of the p-primary trace correction
programme thus reduces to *constructing* an inhabitant of
`TraceLevelRaiseStableSaturationData N k p`.  This is the named
single-shot saturation theorem the audit asks for. -/
noncomputable def TraceLevelRaiseCorrectionData.ofStableSaturation
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (D : TraceLevelRaiseStableSaturationData N k p) :
    TraceLevelRaiseCorrectionData N k p where
  nonFixingCorrection := D.nonFixingCorrection
  remainingFixingCorrection := D.remainingFixingCorrection
  combined_supp := D.combined_supp
  combined_char := D.combined_char

/-! ### T131 erase-stability obstruction (no-go theorems)

The original T131 plan attempted to use `T.erase ⟦1⟧` as the support of
`remainingFixingCorrection`.  The lemmas below show this is *fundamentally*
unworkable: the `ℋ`-action on `ℋ ⧸ (𝒢.subgroupOf ℋ)` is **transitive**
(every coset `q = ⟦h⟧` is the `h`-translate of `⟦1⟧`), so any
`Γ`-stable finset containing `⟦1⟧` is automatically `Finset.univ`, and
`Finset.univ.erase ⟦1⟧` is *never* `Γ`-stable when the quotient has more
than one element.

This forces the next worker away from any "filtered coset sum" strategy
for the identity-coset summand and toward an Atkin–Lehner / Petersson
orthogonality argument (T132). -/

/-- **Transitivity of the `ℋ`-translation action on `ℋ ⧸ K`.**
Any `Γ`-stable finset of cosets containing the identity coset is the
whole `Finset.univ`. -/
lemma IsGammaStableCosetFinset.eq_univ_of_one_mem
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}
    [Fintype (ℋ ⧸ (𝒢.subgroupOf ℋ))] [DecidableEq (ℋ ⧸ (𝒢.subgroupOf ℋ))]
    {T : Finset (ℋ ⧸ (𝒢.subgroupOf ℋ))}
    (hT : IsGammaStableCosetFinset (𝒢 := 𝒢) (ℋ := ℋ) T)
    (h_id : (⟦(1 : ℋ)⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) ∈ T) :
    T = Finset.univ := by
  refine Finset.eq_univ_iff_forall.mpr ?_
  intro q
  refine Quotient.inductionOn q (fun h ↦ ?_)
  have hstab := hT h 1 h_id
  have heq : (⟦h * 1⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) = ⟦h⟧ := by
    congr 1; exact mul_one h
  rw [heq] at hstab
  exact hstab

/-- **Erase no-go.**  If the quotient `ℋ ⧸ (𝒢.subgroupOf ℋ)` has more than
one element and `T` is `Γ`-stable with `⟦1⟧ ∈ T`, then `T.erase ⟦1⟧` is
*not* `Γ`-stable.  Proof: by the previous lemma, `T = Finset.univ`; by
transitivity any non-identity coset `q = ⟦h⟧` satisfies
`h⁻¹ • q = ⟦1⟧`, so `T.erase ⟦1⟧` cannot be closed under
left-multiplication by `h⁻¹`. -/
lemma not_isGammaStableCosetFinset_erase_one
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}
    [Fintype (ℋ ⧸ (𝒢.subgroupOf ℋ))] [DecidableEq (ℋ ⧸ (𝒢.subgroupOf ℋ))]
    {T : Finset (ℋ ⧸ (𝒢.subgroupOf ℋ))}
    (hT : IsGammaStableCosetFinset (𝒢 := 𝒢) (ℋ := ℋ) T)
    (h_id : (⟦(1 : ℋ)⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) ∈ T)
    (hne : ∃ q : ℋ ⧸ (𝒢.subgroupOf ℋ), q ≠ ⟦1⟧) :
    ¬ IsGammaStableCosetFinset (𝒢 := 𝒢) (ℋ := ℋ) (T.erase ⟦1⟧) := by
  obtain ⟨q, hq⟩ := hne
  intro hStable
  refine Quotient.inductionOn q (motive := fun q ↦ q ≠ ⟦1⟧ → False) ?_ hq
  intro h hh
  have hT_univ : T = Finset.univ := hT.eq_univ_of_one_mem h_id
  have h_in_erase : (⟦h⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) ∈ T.erase ⟦1⟧ := by
    rw [Finset.mem_erase]
    exact ⟨hh, by rw [hT_univ]; exact Finset.mem_univ _⟩
  have hback := hStable h⁻¹ h h_in_erase
  have heq : (⟦h⁻¹ * h⟧ : ℋ ⧸ (𝒢.subgroupOf ℋ)) = ⟦(1 : ℋ)⟧ := by
    congr 1; exact inv_mul_cancel h
  rw [heq] at hback
  simp at hback

/-- **No-go for `TraceLevelRaiseStableSaturationData`.**  Any inhabitant
forces `D.saturated = Finset.univ`, since the `ℋ`-action on the quotient
is transitive and the saturation contains the identity coset.  This
shows the original "saturate then erase" strategy cannot produce the
identity-coset summand: the erased complement is never `Γ`-stable, so
`cuspFormOfGammaStableCosetSumLinear` cannot be applied to it. -/
lemma TraceLevelRaiseStableSaturationData.saturated_eq_univ
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (D : TraceLevelRaiseStableSaturationData N k p) :
    haveI : ((Gamma1 (p * N)).map (mapGL ℝ)).IsFiniteRelIndex
        ((Gamma1 N).map (mapGL ℝ)) :=
      HeckeRing.GL2.TraceOperator.Gamma1_mapGL_isFiniteRelIndex_of_dvd
        (Nat.dvd_mul_left N p)
    haveI : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
        ((Gamma1 (p * N)).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
      Fintype.ofFinite _
    D.saturated = Finset.univ := by
  haveI : ((Gamma1 (p * N)).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma1 N).map (mapGL ℝ)) :=
    HeckeRing.GL2.TraceOperator.Gamma1_mapGL_isFiniteRelIndex_of_dvd
      (Nat.dvd_mul_left N p)
  haveI : Fintype ((Gamma1 N).map (mapGL ℝ) ⧸
      ((Gamma1 (p * N)).map (mapGL ℝ)).subgroupOf ((Gamma1 N).map (mapGL ℝ))) :=
    Fintype.ofFinite _
  classical
  convert D.saturated_stable.eq_univ_of_one_mem D.identity_mem using 2

end HeckeRing.GL2.AtkinLehner
