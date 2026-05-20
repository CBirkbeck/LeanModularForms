/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Miyake Theorem 4.6.4 — Conductor theorem (POST-6b)

This file develops the **conductor theorem** of Miyake §4.6.4, the second of
the three sub-results that feed into Miyake's Main Lemma 4.6.8 (which in turn
is the engine of the Strong Multiplicity One theorem 4.6.12).

## Mathematical statement

Following the cusp-form-first formulation from the T035 packet:

> Let `g` be a level-`Γ₁(N)` weight-`k` cusp form lying in the Nebentypus
> eigenspace `cuspFormCharSpace k χ.toUnitHom`, whose `q`-expansion is
> supported only on multiples of `l` (i.e., the coefficients at every `n`
> not divisible by `l` vanish). Then:
>
>  * if `l * χ.conductor ∣ N`, then `χ` factors as
>    `χ = changeLevel _ χ_low` for a unique
>    `χ_low : DirichletCharacter ℂ (N / l)`, and there is a level-`N/l`
>    cusp form `g'` lying in `cuspFormCharSpace k χ_low.toUnitHom`
>    with `g = levelRaise (N/l) l k g'`;
>  * otherwise (`l * χ.conductor ∤ N`), `g = 0`.

Reference: Miyake, *Modular Forms*, Theorem 4.6.4.

## Imports

By design this file imports only:

* `LeanModularForms.HeckeRIngs.GL2.LevelRaise` — the level-raising operator
  `levelRaise` and its matrix infrastructure (extracted by ticket T037 from
  `Newforms.lean` to avoid the heavy `AdjointTheory.lean` /
  `BlockBijection.lean` chain).
* `LeanModularForms.HeckeRIngs.GL2.Gamma1Pair` — character spaces
  `modFormCharSpace` / `cuspFormCharSpace` and the Nebentypus bridges
  `*_iff_nebentypus`.
* `Mathlib.NumberTheory.DirichletCharacter.Basic` — `DirichletCharacter`,
  `conductor`, `changeLevel`, `FactorsThrough`, `primitiveCharacter`.
* `Mathlib.NumberTheory.ModularForms.QExpansion` — `qExpansion` and the
  vanishing/uniqueness lemmas `qExpansion_eq_zero_iff` etc.

This file deliberately does NOT import `Newforms.lean`, `AdjointTheory.lean`,
or `BlockBijection.lean`. The point is to keep POST-6b independent of the
T001/Epic D blocker chain.

## Main API (this file)

Period-1 invariance for `Γ₁(N)`-cusp forms:

* `ModularGroup_T_mem_Gamma1` — `T = [[1, 1], [0, 1]] ∈ Γ₁(N)`.
* `ModularGroup_T_zpow_mem_Gamma1` — `T ^ n ∈ Γ₁(N)` for every `n : ℤ`.
* `cuspForm_T_slash_eq_self` — the slash action of `T` on a `Γ₁(N)`-cusp
  form is the identity.
* `cuspForm_T_zpow_slash_eq_self` — the same for `T ^ n`.

(The pointwise evaluation helpers `levelRaiseFun_apply`,
`denom_levelRaiseMatrix`, `levelRaiseMatrix_det_pos`,
`abs_levelRaiseMatrix_det_val`, and `σ_levelRaiseMatrix`, plus the
T043 surjectivity / injectivity helpers `coe_levelRaiseMatrix_smul`,
`exists_levelRaiseMatrix_smul_eq`, and `levelRaiseFun_injective`,
all live in `LevelRaise.lean` where they belong as part of the
level-raise API.)

Case A conductor-lowering bridges:

* `dvd_lower_left_of_dvd_of_mem_Gamma0` — `l ∣ N` + `γ ∈ Γ₀(N)` gives
  `l ∣ γ.val 1 0`, the divisibility hypothesis needed by
  `levelRaiseConjOfDvd`.
* `conductor_slash_levelRaise_eq` — the **level-raised** conductor-lowering
  slash identity (T042). If `g ∈ modFormCharSpace k χ.toUnitHom` factors as
  `⇑g = levelRaiseFun l k f` and `l ∣ N`, then for every `γ ∈ Γ₀(N)`,
  ```
  levelRaiseFun l k (f ∣[k] mapGL ℝ γ̃) = (χ d_γ) • levelRaiseFun l k f
  ```
  where `γ̃ = α_l γ α_l⁻¹`.
* `smul_levelRaiseFun` — small commutation lemma:
  `c • levelRaiseFun l k f = levelRaiseFun l k (c • f)`.
* `conductor_slash_eq` — the **unlifted** conductor-lowering slash identity
  (T043). Same hypotheses as `conductor_slash_levelRaise_eq`, but the
  conclusion is the un-rescaled Nebentypus identity for `f` itself:
  ```
  f ∣[k] mapGL ℝ γ̃ = (χ d_γ) • f.
  ```
  Obtained by combining `conductor_slash_levelRaise_eq` with
  `smul_levelRaiseFun` and `LevelRaise.levelRaiseFun_injective`.

Case A inverse formula and holomorphy inheritance (T044):

* `fun_eq_apply_levelRaiseMatrix_inv_smul` — pointwise inverse formula:
  `f τ = g (α_l⁻¹ • τ)` from `⇑g = levelRaiseFun l k f`.
* `fun_eq_levelRaiseMatrix_inv_smul` — functional version: `f` equals the
  precomposition of `g` with the `α_l⁻¹`-action.
* `levelRaiseMatrix_inv_det_pos` — `det α_l⁻¹ = 1/l > 0`.
* `mdifferentiable_of_levelRaiseFun_eq` — holomorphy of `f` from
  holomorphy of `g`, via the inverse formula plus
  `UpperHalfPlane.mdifferentiable_smul`.
* `mdifferentiable_of_modularForm_levelRaiseFun_eq` — specialisation
  with `g : ModularForm`, where holomorphy is automatic.

Case A lowered Dirichlet character (T044):

* `loweredCharacter` — given `χ.FactorsThrough (N/l)`, the unique lower
  level `χ_low : DirichletCharacter ℂ (N/l)` with `χ = changeLevel _ χ_low`.
* `changeLevel_loweredCharacter` — re-raising recovers `χ`.
* `toUnitHom_loweredCharacter` — bridge between `χ.toUnitHom` and
  `χ_low.toUnitHom ∘ ZMod.unitsMap _`.

Case A T-conjugate slash bridge (T044 continuation, the second main
deliverable of T044):

* `slashStabilizerOfFun` (private) — the subgroup of `SL(2, ℤ)` whose
  `mapGL ℝ`-image acts trivially on `f` via the slash. Used to extend
  the period-1 hypothesis to integer powers via `Subgroup.zpow_mem`.
* `slash_T_zpow_eq_self_of_slash_T_eq` — given `f ∣[k] T = f`, the slash
  by every integer power of `T` is also trivial: `f ∣[k] T^j = f`.
* `conductor_slash_T_conj_eq` — the central T-conjugate slash bridge:
  under the Case A hypotheses plus `f ∣[k] T = f` (Miyake's separate
  period-1 hypothesis on `f`, NOT inherited from `g`), the slash
  identity extends to all matrices of the form `T^i · γ̃ · T^j`:
  ```
  f ∣[k] (T^i · γ̃ · T^j) = (χ d_γ) • f.
  ```
  The character value is unchanged because `χ` only sees the (1,1)-entry
  of `γ`, which is preserved under both T-translation and α_l-conjugation.

Lowered slash field — full Γ₀(N/l) coverage (T046):

* `conductor_slash_eq_of_mem_Gamma0_div` — combining the T044 slash
  bridge with the T046 group factorisation
  (`LevelRaise.exists_T_levelRaiseConj_T_factor`), the slash identity
  extends to ALL of `Γ₀(N/l)`:
  ```
  ∀ γ' ∈ Γ₀(N/l), ∃ γ ∈ Γ₀(N),
    f ∣[k] mapGL ℝ γ' = (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) • f.
  ```

Lowered character collapse + boundedness at i∞ (T048):

* `conductor_slash_eq_self_of_mem_Gamma1_div` — under the additional
  `χ.FactorsThrough (N/l)` hypothesis (the Case A factor-through
  condition), the slash identity collapses to the IDENTITY for every
  `δ ∈ Γ₁(N/l)`:
  ```
  ∀ δ ∈ Γ₁(N/l), f ∣[k] mapGL ℝ δ = f.
  ```
  This is the FULL slash field for the lowered modular form bundling.
  Proof: γ_lift's (1,1) entry mod (N/l) is δ.val 1 1 mod (N/l) = 1 (by
  Γ₁(N/l)-membership), so `χ_low(1) = 1`.
* `coe_levelRaiseMatrix_inv_smul`, `im_levelRaiseMatrix_inv_smul` —
  helpers for the inverse `α_l⁻¹`-action: scaling the ℂ-coordinate
  by `1/l`.
* `isBoundedAtImInfty_of_levelRaiseFun_eq` — boundedness at the cusp
  `i∞` transfers from `g` to `f` via the substitution `τ ↦ α_l⁻¹ • τ`
  (which sends `Im(τ)` to `Im(τ)/l`).

Slash equation toward all-cusp boundedness (T048 continuation):

* `σ_levelRaiseMatrix_inv` — `σ α_l⁻¹ = id` (positive determinant `1/l`).
* `slash_inv_eq_smul_of_levelRaiseFun_eq` — the **inverse-slash
  equation**: `g ∣[k] α_l⁻¹ = (l^(1-k)) • f`. Direct slash-composition
  proof using `g = (l^(1-k)) • (f ∣[k] α_l)` and `α_l * α_l⁻¹ = 1`.
* `slash_eq_of_levelRaiseFun_eq` — the **slash-by-SL reduction**:
  ```
  f ∣[k] mapGL ℝ A = (l^(k-1)) • g ∣[k] (α_l⁻¹ * mapGL ℝ A)
  ```
  for every `A : SL(2, ℤ)`. Combines the inverse-slash equation with
  scalar pull-out and slash composition.
* `isBoundedAtImInfty_slash_iff_levelRaiseFun_eq` — the boundedness
  reduction at i∞:
  ```
  IsBoundedAtImInfty (f ∣[k] mapGL ℝ A) ↔
    IsBoundedAtImInfty (g ∣[k] (α_l⁻¹ * mapGL ℝ A))
  ```
  for every `A : SL(2, ℤ)`. Direct from `slash_eq_of_levelRaiseFun_eq`
  + scalar-multiplication preserves boundedness.

All-cusp boundedness and lowered modular form bundle (T059):

* `cuspWitnessLevelRaiseInv` — the explicit `SL(2, ℤ)` witness
  whose `mapGL ℝ`-image acts on `∞` to give the same point as
  `(α_l)⁻¹ * mapGL ℝ A`. Constructed via `IsCoprime.exists_SL2_col`
  from the primitive form of `(A.val 0 0, l * A.val 1 0)`.
* `isCusp_levelRaiseMatrix_inv_mul_mapGL_smul_infty` — the cusp
  `(α_l⁻¹ * mapGL ℝ A) • ∞` is a cusp of every arithmetic subgroup
  `Γ : Subgroup (GL (Fin 2) ℝ)`. Reduces to `IsCusp _ 𝒮ℒ` via
  `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` and
  `isCusp_SL2Z_iff'` with the explicit witness above.
* `isBoundedAtImInfty_slash_levelRaiseMatrix_inv_mul_mapGL` —
  application of `g.bdd_at_cusps'` at the cusp witness yields
  `IsBoundedAtImInfty (g ∣[k] (α_l⁻¹ * mapGL ℝ A))`.
* `isBoundedAtImInfty_slash_mapGL_of_levelRaiseFun_eq` — combining the
  T048 reduction `isBoundedAtImInfty_slash_iff_levelRaiseFun_eq` with the
  preceding lemma yields `IsBoundedAtImInfty (f ∣[k] mapGL ℝ A)` for
  every `A : SL(2, ℤ)`.
* `bdd_at_cusps_of_levelRaiseFun_eq` — the **all-cusp boundedness
  theorem**: `c.IsBoundedAt f k` for every cusp `c` of
  `(Gamma1 (N/l)).map (mapGL ℝ)`. Discharges the `bdd_at_cusps'` field
  via `OnePoint.isBoundedAt_iff_exists_SL2Z` and `ModularForm.SL_slash`.
* `conductorTheoremCaseA_modularForm` — the **Case A lowered modular
  form bundle**: combines the slash-invariance field
  (`conductor_slash_eq_self_of_mem_Gamma1_div`), holomorphy
  (`mdifferentiable_of_modularForm_levelRaiseFun_eq`), and cusp
  regularity (`bdd_at_cusps_of_levelRaiseFun_eq`) into the structural
  `ModularForm ((Gamma1 (N/l)).map (mapGL ℝ)) k` whose underlying
  function is `f`.
* `conductorTheoremCaseA_modularForm_apply` — the bundle's coercion is
  `f` (definitionally, by `rfl`).

CuspForm version of Case A (T064):

* `isZeroAtImInfty_of_levelRaiseFun_eq` — direct zero-at-`i∞` transfer:
  if `g` vanishes at `i∞` and `g = levelRaiseFun l k f`, then so does `f`.
* `isZeroAtImInfty_slash_iff_levelRaiseFun_eq` — slash zero-at-`i∞`
  reduction: `IsZeroAtImInfty (f ∣[k] mapGL ℝ A) ↔
  IsZeroAtImInfty (g ∣[k] (α_l⁻¹ * mapGL ℝ A))`.
* `isZeroAtImInfty_slash_levelRaiseMatrix_inv_mul_mapGL` — application
  of `g.zero_at_cusps'` for `g : CuspForm` at the shared cusp witness
  yields `IsZeroAtImInfty (g ∣[k] (α_l⁻¹ * mapGL ℝ A))`.
* `isZeroAtImInfty_slash_mapGL_of_levelRaiseFun_eq` — combining the
  reduction with the preceding lemma yields
  `IsZeroAtImInfty (f ∣[k] mapGL ℝ A)` for every `A : SL(2, ℤ)`.
* `zero_at_cusps_of_levelRaiseFun_eq` — the **all-cusp vanishing
  theorem**: `c.IsZeroAt f k` for every cusp `c` of
  `(Gamma1 (N/l)).map (mapGL ℝ)`.
* `cuspFormToModularForm` — local upgrade `CuspForm → ModularForm` (a
  cusp form is automatically a modular form via
  `IsZeroAtImInfty → IsBoundedAtImInfty`); kept local to avoid the heavy
  `AdjointTheory` chain.
* `cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace` —
  the upgrade preserves Nebentypus character space membership, both
  via `*_iff_nebentypus`.
* `conductorTheoremCaseA_cuspForm` — the **Case A lowered cusp form
  bundle**: combines slash invariance, holomorphy, and the new
  zero-at-cusps regularity into the structural
  `CuspForm ((Gamma1 (N/l)).map (mapGL ℝ)) k` whose underlying function
  is `f`.
* `conductorTheoremCaseA_cuspForm_apply` — the bundle's coercion is `f`
  (definitionally, by `rfl`).

Case B (vanishing) preparation (T065):

* `exists_unit_of_not_factorsThrough` — from `¬ χ.FactorsThrough d`,
  extract `u : (ZMod N)ˣ` with `ZMod.unitsMap u = 1` (i.e., `u` in the
  kernel of unit-group reduction) and `χ.toUnitHom u ≠ 1`.
* `levelRaiseConjOfDvd_mem_Gamma1_div_of_mem_ker` — the **structural
  ascent**: for `γ ∈ Γ₀(N)` with `γ.val 1 1 ≡ 1 mod (N/l)`, the
  conjugate `levelRaiseConjOfDvd l γ : SL(2, ℤ)` lies in `Γ₁(N/l)`.
* `case_B_slash_relation` — the **central slash relation theorem**:
  under `¬ χ.FactorsThrough (N/l)`, there exist `δ ∈ Γ₁(N/l)` and `c : ℂ`
  with `c ≠ 1` such that `f ∣[k] mapGL ℝ δ = c • f`. The witness is
  `δ = α_l γ_u α_l⁻¹` for some `γ_u ∈ Γ₀(N)` lifting a problematic unit.
* `fun_eq_zero_of_two_multipliers` — the **algebraic contradiction**:
  if `f ∣[k] M = c₁ • f = c₂ • f` with `c₁ ≠ c₂`, then `f = 0`.
  Captures the algebraic core of the Case B argument.
* `case_B_vanishing_of_two_multipliers` — the **conditional Case B
  vanishing**: under the Case B hypothesis, `f = 0` provided we can
  produce a SECOND scalar `c'` (different from the first) such that
  `f ∣[k] mapGL ℝ δ = c' • f` for the witness matrix `δ`. Discharged
  unconditionally by T072 below.

Constructive Case B closure (T071 + T072):

* `gamma0LiftLowerLeftN N u` — controlled `Γ₀(N)` lift of
  `u : (ZMod N)ˣ` with `(1, 0)` entry equal to `N` (Bezout matrix).
* `case_B_slash_relation_with_controlled_lift` — refined
  `case_B_slash_relation` exposing `γ_u.val 1 0 = N` for downstream
  matrix arithmetic.
* `exists_alt_unit_in_coset_with_char_separation` — for `u : (ZMod N)ˣ`
  there is `u'` in the same `unitsMap`-coset with `χ(u') ≠ χ(u)`.
* `T_shift_divisibility_eq_iff` — algebraic restatement of the
  `(i, j)`-shift divisibility constraint.
* `t_factor_matrix_identity` — the matrix identity
  `[[a, l*b; Nl, e]] = T^i * [[a', l*b'; Nl, e']] * T^j` from the
  shift / determinant relations.
* `exists_T_factor_with_char_separation` — given the Case B hypothesis,
  produce explicit `(i, j)` and a separating unit `u'` such that
  `levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u) =
   T^i * levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u') * T^j` AND
  `χ(u') ≠ χ(u)`.
* `conductorTheoremCaseB_vanishing` — the **fully-closed Case B
  vanishing theorem**: under `¬ χ.FactorsThrough (N/l)` plus the
  period-1 hypothesis on `f`, the candidate lower-level form is
  identically zero.

Conductor theorem dichotomy (T075):

* `conductor_theorem_dichotomy` — the **full Miyake §4.6.4 statement**
  for `g : ModularForm`: EITHER `χ` factors through level `N/l` AND
  `f` bundles into a lowered `ModularForm` (Case A), OR `f = 0`
  (Case B). Direct combination of `conductorTheoremCaseA_modularForm` +
  `conductorTheoremCaseB_vanishing` via `by_cases`.
* `conductor_theorem_dichotomy_cuspForm` — the **CuspForm flavor** of
  the dichotomy, using `conductorTheoremCaseA_cuspForm` (T064) and
  reducing the Case B branch to the modular-form vanishing via
  `cuspFormToModularForm`.

Lowered character-space packaging (T077):

* `conductorTheoremCaseA_modularForm_mem_modFormCharSpace` — the Case A
  bundle for `g : ModularForm` lies in
  `modFormCharSpace k (loweredCharacter h_fac).toUnitHom`. Proof
  combines `exists_T_levelRaiseConj_T_factor`,
  `conductor_slash_T_conj_eq`, `toUnitHom_loweredCharacter`, and the
  private helper `unitsMap_Gamma0MapUnits_lift_eq_of_diag` (which
  matches the `Gamma0MapUnits` images under the unit-group reduction).
* `conductorTheoremCaseA_cuspForm_mem_cuspFormCharSpace` — the
  CuspForm flavor.
* `conductor_theorem_dichotomy_strong` /
  `conductor_theorem_dichotomy_cuspForm_strong` — strengthened
  dichotomy variants whose Case A branch additionally certifies the
  lowered character-space membership of the lowered bundle. These are
  the structural inputs to Miyake's Main Lemma 4.6.8 (POST-6e).

## Status

POST-6b is **feature-complete**. All declarations in this file are
sorry-free, axiom-clean (only `propext`, `Classical.choice`,
`Quot.sound`).

* **Case A** (T041–T064) — `f` bundles into the lowered modular/cusp
  form via `conductorTheoremCaseA_modularForm` /
  `conductorTheoremCaseA_cuspForm` under
  `χ.FactorsThrough (N/l)`.
* **Case B vanishing** (T065 + T071 + T072) — `f = 0` under
  `¬ χ.FactorsThrough (N/l)`, packaged as
  `conductorTheoremCaseB_vanishing`. The proof composes
  `case_B_slash_relation_with_controlled_lift` with
  `exists_T_factor_with_char_separation` and the algebraic
  two-multiplier contradiction.
* **Dichotomy** (T075) — `conductor_theorem_dichotomy` (modular form
  flavor) and `conductor_theorem_dichotomy_cuspForm` (cusp form flavor)
  combine the two cases into the full Miyake §4.6.4 statement.
* **Lowered character-space packaging** (T077) — the strengthened
  variants `conductor_theorem_dichotomy_strong` and
  `conductor_theorem_dichotomy_cuspForm_strong` additionally certify that
  the Case A bundle lies in `modFormCharSpace` /
  `cuspFormCharSpace` of the lowered Dirichlet character
  `loweredCharacter h_fac`.

These strong dichotomy theorems are the structural input to Miyake's
Main Lemma 4.6.8 (POST-6e): given a level-`N` eigenform `g` with
q-expansion supported on multiples of `l` and conductor
`l * χ.conductor ∣ N`, Case A produces the lowered eigenform at
`Γ₁(N/l)` carrying the lowered Nebentypus character; Case B handles the
contrapositive direction.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup CuspForm

open scoped MatrixGroups ModularForm Pointwise Manifold

noncomputable section

namespace HeckeRing.GL2

variable {N : ℕ} {k : ℤ}

/-! ### Period-1 invariance of `Γ₁(N)`-cusp forms

Every `Γ₁(N)`-cusp form is invariant under the modular `T = [[1, 1], [0, 1]]`
matrix and its powers. This is the abstract statement of "q-expansion
period 1 at the cusp `i∞`" used by Miyake §4.6.4 (Conductor theorem) when
producing the period-`(1/l)` contradiction in Case B. -/

/-- The modular `T = [[1, 1], [0, 1]]` matrix lies in `Γ₁(N)` for every level. -/
lemma ModularGroup_T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.coe_T]

/-- The integer power `T^n = [[1, n], [0, 1]]` lies in `Γ₁(N)` for every `n : ℤ`
and every level `N`. -/
lemma ModularGroup_T_zpow_mem_Gamma1 (N : ℕ) (n : ℤ) :
    ModularGroup.T ^ n ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.coe_T_zpow]

/-- A `Γ₁(N)`-cusp form is invariant under the slash action by `T`:
`f ∣[k] T = f`. This is the basic "period-1 at `i∞`" statement of
Miyake §4.6.4. -/
lemma cuspForm_T_slash_eq_self [NeZero N]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] (ModularGroup.T : SL(2, ℤ)) = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _
    ⟨ModularGroup.T, ModularGroup_T_mem_Gamma1 N, rfl⟩

/-- A `Γ₁(N)`-cusp form is invariant under the slash action by every integer
power of `T`: `f ∣[k] T^n = f`. -/
lemma cuspForm_T_zpow_slash_eq_self [NeZero N] (n : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] ((ModularGroup.T ^ n : SL(2, ℤ))) = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _
    ⟨ModularGroup.T ^ n, ModularGroup_T_zpow_mem_Gamma1 N n, rfl⟩

/-! ### Case A conductor-lowering bridge

The central lemma in the Case A direction of Miyake §4.6.4: a level-`Γ₁(N)`
modular form `g` lying in the Nebentypus eigenspace `modFormCharSpace k χ`
which factors as `g(τ) = f(l·τ)` (i.e., `⇑g = levelRaiseFun l k f`) gives
rise — for every `γ ∈ Γ₀(N)` and `l ∣ N` — to a level-raised slash identity
for the un-scaled function `f`:

```
levelRaiseFun l k (f ∣[k] mapGL ℝ γ̃) = (χ d_γ) • levelRaiseFun l k f.
```

Combining the new `slash_mapGL_levelRaiseFun` bridge from `LevelRaise.lean`
with the local `modFormCharSpace_iff_nebentypus` Nebentypus translation. -/

/-- Helper: if `l ∣ N` and `γ ∈ Γ₀(N)`, then `l ∣ γ.val 1 0`. -/
private lemma dvd_lower_left_of_dvd_of_mem_Gamma0
    {l N : ℕ} (h_dvd : l ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    (l : ℤ) ∣ γ.val 1 0 := by
  rw [Gamma0_mem] at hγ
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd) h

/-- **Case A conductor-lowering bridge (level-raised slash identity).**

Suppose `g : ModularForm Γ₁(N) k` lies in the Nebentypus eigenspace
`modFormCharSpace k χ.toUnitHom` (so `g ∣[k] γ = χ(d_γ) • g` for every
`γ ∈ Γ₀(N)`), and suppose furthermore that the underlying function of `g`
is the level-raise of some `f : ℍ → ℂ`: `⇑g = levelRaiseFun l k f`. Then for
every `γ ∈ Γ₀(N)` (with the divisibility `l ∣ N` automatic from the
structure), the level-raise of the slash action of `mapGL ℝ γ̃` on `f`
equals the Nebentypus-twisted level-raise of `f`:

```
levelRaiseFun l k (f ∣[k] mapGL ℝ γ̃) = (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ)
                                          • levelRaiseFun l k f
```

where `γ̃ = α_l γ α_l⁻¹` is built by `levelRaiseConjOfDvd`. This is the
"lifted" form of the conductor lowering: it expresses the slash identity at
the level-`N/l` matrix `γ̃` modulo the level-raise. The corresponding
"unlifted" identity `f ∣[k] mapGL ℝ γ̃ = χ(d_γ) • f` follows by
post-composing with `levelRaiseFun_apply` and the surjectivity of the
`α_l`-action on `ℍ`; this reduction will land in a follow-on ticket. -/
lemma conductor_slash_levelRaise_eq (l N : ℕ) [NeZero l] [NeZero N]
    (h_dvd : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    levelRaiseFun l k (f ∣[k] (mapGL ℝ
        (levelRaiseConjOfDvd l γ
          (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγ))
        : GL (Fin 2) ℝ)) =
      (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) • levelRaiseFun l k f := by
  have h_neb := (modFormCharSpace_iff_nebentypus k χ.toUnitHom g).mp hg_char ⟨γ, hγ⟩
  -- h_neb : ⇑g ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) =
  --           (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) • ⇑g
  rw [hg_eq, slash_mapGL_levelRaiseFun] at h_neb
  exact h_neb

/-! ### Unlifted Case A bridge

The level-raised slash identity from `conductor_slash_levelRaise_eq` cancels
to a clean unlifted Nebentypus relation for `f` itself by injectivity of
`levelRaiseFun l k`. This is the form most useful downstream: it gives a
`Γ₀(N/l)`-invariance statement for `f` directly, without the level-raise
wrapper. -/

/-- Auxiliary: the scalar multiplication commutes with the level-raise operator.
For `c : ℂ` and `f : ℍ → ℂ`, `c • levelRaiseFun l k f = levelRaiseFun l k (c • f)`.
The slash action by `α_l` (positive determinant, σ trivial) commutes with the
complex scalar action. -/
lemma smul_levelRaiseFun (l : ℕ) [NeZero l] (k : ℤ) (c : ℂ)
    (f : UpperHalfPlane → ℂ) :
    c • levelRaiseFun l k f = levelRaiseFun l k (c • f) := by
  funext τ
  rw [Pi.smul_apply, levelRaiseFun_apply, levelRaiseFun_apply, smul_eq_mul,
    Pi.smul_apply, smul_eq_mul]

/-- **Unlifted Case A conductor-lowering bridge.** Same hypotheses as
`conductor_slash_levelRaise_eq`, but the conclusion is the un-rescaled
Nebentypus identity for `f`:

```
f ∣[k] mapGL ℝ γ̃ = (χ d_γ) • f
```

where `γ̃ = α_l γ α_l⁻¹`. Obtained from the lifted form by cancelling the
`levelRaiseFun l k` wrapper via `levelRaiseFun_injective` and the auxiliary
`smul_levelRaiseFun`. -/
lemma conductor_slash_eq (l N : ℕ) [NeZero l] [NeZero N]
    (h_dvd : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    f ∣[k] (mapGL ℝ
        (levelRaiseConjOfDvd l γ
          (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγ))
        : GL (Fin 2) ℝ) =
      (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) • f := by
  have h_lifted := conductor_slash_levelRaise_eq l N h_dvd k χ f g hg_char hg_eq γ hγ
  rw [smul_levelRaiseFun] at h_lifted
  exact levelRaiseFun_injective l k h_lifted

/-! ### Inverse formula and holomorphy inheritance for `f`

The Case A construction needs to bundle `f : ℍ → ℂ` (the lower-level
candidate) into a `ModularForm` / `CuspForm` at level `Γ₁(N/l)`. The
slash-invariance field has been substantially closed via the T043
`conductor_slash_eq`. The next two structural fields needed are
**holomorphy** (`MDifferentiable`) and the **cusp condition**
(`bdd_at_cusps'` for modular forms, `zero_at_cusps'` for cusp forms).

This section provides the inverse formula `f τ = g (α_l⁻¹ • τ)` (which
follows from `levelRaiseFun_apply` plus `mul_inv_cancel + one_smul`), and
uses it to inherit holomorphy of `f` from holomorphy of `g` via the
Mathlib lemma `UpperHalfPlane.mdifferentiable_smul` for the
positive-determinant action `α_l⁻¹ • _ : ℍ → ℍ`. -/

/-- **Inverse formula for the level-raise.** From `⇑g = levelRaiseFun l k f`,
recover `f` as the precomposition of `g` with the inverse `α_l⁻¹`-action:
`f τ = g (α_l⁻¹ • τ)`.

This is the cleanest pointwise inversion of `levelRaiseFun_apply`
(`g τ = f (α_l • τ)`): substituting `τ ← α_l⁻¹ • τ'` and using
`α_l · α_l⁻¹ = 1`. -/
lemma fun_eq_apply_levelRaiseMatrix_inv_smul (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ) (hg : g = levelRaiseFun l k f)
    (τ : UpperHalfPlane) :
    f τ = g ((levelRaiseMatrix l)⁻¹ • τ) := by
  rw [hg, levelRaiseFun_apply, smul_smul,
    mul_inv_cancel (levelRaiseMatrix l), one_smul]

/-- Functional equality version of `fun_eq_apply_levelRaiseMatrix_inv_smul`:
`f = (fun τ => g (α_l⁻¹ • τ))`. -/
lemma fun_eq_levelRaiseMatrix_inv_smul (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ) (hg : g = levelRaiseFun l k f) :
    f = fun τ => g ((levelRaiseMatrix l)⁻¹ • τ) := by
  funext τ
  exact fun_eq_apply_levelRaiseMatrix_inv_smul l k f g hg τ

/-- Positive determinant of `(levelRaiseMatrix l)⁻¹`: the inverse has det
`1 / l > 0`. Used to invoke `UpperHalfPlane.mdifferentiable_smul` for the
inverse action. -/
lemma levelRaiseMatrix_inv_det_pos (l : ℕ) [NeZero l] :
    (0 : ℝ) < (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l)⁻¹ : ℝ) := by
  rw [show (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l)⁻¹ : ℝˣ) =
      (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l))⁻¹ from
    map_inv Matrix.GeneralLinearGroup.det _]
  rw [Units.val_inv_eq_inv_val]
  exact inv_pos.mpr (levelRaiseMatrix_det_pos l)

/-- **Holomorphy inheritance.** If `g : ℍ → ℂ` is holomorphic
(`MDifferentiable`) and `g = levelRaiseFun l k f`, then `f` is also
holomorphic on `ℍ`.

Proof: `f τ = g (α_l⁻¹ • τ)` (by `fun_eq_levelRaiseMatrix_inv_smul`), and
the action `τ ↦ α_l⁻¹ • τ` is `MDifferentiable` (by Mathlib's
`UpperHalfPlane.mdifferentiable_smul` since `det α_l⁻¹ > 0`), so `f` is
the composition of two `MDifferentiable` maps. -/
lemma mdifferentiable_of_levelRaiseFun_eq (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ)
    (hg_diff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hg_eq : g = levelRaiseFun l k f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  rw [fun_eq_levelRaiseMatrix_inv_smul l k f g hg_eq]
  exact hg_diff.comp
    (UpperHalfPlane.mdifferentiable_smul (levelRaiseMatrix_inv_det_pos l))

/-- **Holomorphy of `f` from a `ModularForm` `g`.** Specialisation of
`mdifferentiable_of_levelRaiseFun_eq` to the case where `g` is bundled as a
`ModularForm`: holomorphy is automatic via `ModularFormClass.holo`. -/
lemma mdifferentiable_of_modularForm_levelRaiseFun_eq
    {Γ : Subgroup (GL (Fin 2) ℝ)} (l : ℕ) [NeZero l] (k : ℤ)
    (f : UpperHalfPlane → ℂ) (g : ModularForm Γ k)
    (hg_eq : ⇑g = levelRaiseFun l k f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  mdifferentiable_of_levelRaiseFun_eq l k f ⇑g
    (ModularFormClass.holo g) hg_eq

/-! ### The lowered Dirichlet character `χ_low`

When `χ : DirichletCharacter ℂ N` factors through level `N/l` (the Case A
hypothesis `l * χ.conductor ∣ N`, equivalently `χ.FactorsThrough (N/l)`),
its image at the lowered level is captured by `FactorsThrough.χ₀`. The
slash-action conclusion of `conductor_slash_eq` mentions `χ.toUnitHom` at
the *original* level `N`; this section provides the bridge to the lowered
character `χ_low` via `changeLevel_eq_cast_of_dvd`, so downstream code can
state Nebentypus identities for `f` purely in terms of
`χ_low.toUnitHom : (ZMod (N/l))ˣ →* ℂˣ`. -/

/-- The Case A lowered character: when `χ` factors through level `N/l`,
this is the unique `χ_low : DirichletCharacter ℂ (N/l)` with
`χ = changeLevel _ χ_low`. Just `FactorsThrough.χ₀`. -/
noncomputable def loweredCharacter {N : ℕ} {l : ℕ}
    {χ : DirichletCharacter ℂ N} (hfac : χ.FactorsThrough (N / l)) :
    DirichletCharacter ℂ (N / l) :=
  hfac.χ₀

/-- `loweredCharacter hfac` re-raises to `χ` along the canonical level-change. -/
lemma changeLevel_loweredCharacter {N : ℕ} {l : ℕ}
    {χ : DirichletCharacter ℂ N} (hfac : χ.FactorsThrough (N / l)) :
    DirichletCharacter.changeLevel hfac.dvd (loweredCharacter hfac) = χ :=
  hfac.eq_changeLevel.symm

/-- The unit-group hom of `χ_low` agrees with `χ.toUnitHom` after composition
with the unit-group reduction `(ZMod N)ˣ → (ZMod (N/l))ˣ`:

```
χ.toUnitHom = χ_low.toUnitHom ∘ ZMod.unitsMap (N/l ∣ N).
```

Direct unfolding of `changeLevel_toUnitHom` after rewriting via
`changeLevel_loweredCharacter`. This is the bridge that lets downstream
code rephrase "`χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩)`" (which appears in
the conclusion of `conductor_slash_eq`) as
"`χ_low.toUnitHom (ZMod.unitsMap _ (Gamma0MapUnits ⟨γ, hγ⟩))`" — which
in turn, when `γ ∈ Γ₀(N/l)` lifts a level-`N/l` γ̃, makes the
"d-coordinate" naturally live in `(ZMod (N/l))ˣ`. -/
lemma toUnitHom_loweredCharacter {N : ℕ} {l : ℕ}
    {χ : DirichletCharacter ℂ N} (hfac : χ.FactorsThrough (N / l)) :
    χ.toUnitHom =
      (loweredCharacter hfac).toUnitHom.comp (ZMod.unitsMap hfac.dvd) := by
  conv_lhs => rw [← changeLevel_loweredCharacter hfac]
  exact DirichletCharacter.changeLevel_toUnitHom (χ := loweredCharacter hfac) hfac.dvd

/-! ### Slash bridge under T-conjugates of α_l-conjugation image

The Case A goal is to derive the slash-invariance of `f` under all of
`Γ₁(N/l)`. This requires combining (a) the slash identity for matrices
in the α_l-conjugation image (provided by `conductor_slash_eq` from T043),
and (b) the period-1 hypothesis for `f` (a SEPARATE Miyake hypothesis,
NOT inherited from `g = levelRaiseFun l k f`).

This section provides the slash bridge for matrices of the form
`T^i · γ̃ · T^j` (where `γ̃` is in the α_l-conjugation image) — sorry-free,
immediate from these two ingredients. The full coverage of `Γ₁(N/l)`
requires a separate group factorisation lemma showing that every
`γ' ∈ Γ₀(N/l)` decomposes (via left + right T multiplication) into an
α_l-image; that lemma is documented as the next sub-obligation. -/

/-- The set of `SL(2, ℤ)`-elements `γ` for which the slash action of
`mapGL ℝ γ` on `f` is trivial forms a subgroup. Used to extend the
period-1 hypothesis `f ∣[k] T = f` to all integer powers `T^j`. -/
private def slashStabilizerOfFun (k : ℤ) (f : UpperHalfPlane → ℂ) :
    Subgroup SL(2, ℤ) where
  carrier := { γ | f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = f }
  one_mem' := by
    show f ∣[k] (mapGL ℝ (1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = f
    rw [map_one, SlashAction.slash_one]
  mul_mem' := fun {a b} ha hb => by
    show f ∣[k] (mapGL ℝ (a * b) : GL (Fin 2) ℝ) = f
    rw [map_mul, SlashAction.slash_mul, ha, hb]
  inv_mem' := fun {a} ha => by
    show f ∣[k] (mapGL ℝ a⁻¹ : GL (Fin 2) ℝ) = f
    have h_mul := SlashAction.slash_mul k
      (mapGL ℝ a) (mapGL ℝ a⁻¹) f
    rw [show (mapGL ℝ a : GL (Fin 2) ℝ) * mapGL ℝ a⁻¹ = 1 from by
        rw [← map_mul, mul_inv_cancel, map_one],
      SlashAction.slash_one, ha] at h_mul
    exact h_mul.symm

/-- Given the period-1 hypothesis `f ∣[k] T = f`, the slash by every integer
power of `T` is also trivial: `f ∣[k] T^j = f` for all `j : ℤ`. Proof via
the slash-stabilizer subgroup: `T` is in the stabilizer by hypothesis, so
`T^j` is in it for every `j : ℤ` by `Subgroup.zpow_mem`. -/
lemma slash_T_zpow_eq_self_of_slash_T_eq (k : ℤ) (f : UpperHalfPlane → ℂ)
    (hf : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) (j : ℤ) :
    f ∣[k] (mapGL ℝ (ModularGroup.T ^ j) : GL (Fin 2) ℝ) = f := by
  have hT_mem : ModularGroup.T ∈ slashStabilizerOfFun k f := hf
  exact zpow_mem hT_mem j

/-- **Slash bridge for T-conjugates of the α_l-conjugation image.**

Given the Case A hypotheses (`g ∈ modFormCharSpace k χ.toUnitHom`,
`⇑g = levelRaiseFun l k f`, `l ∣ N`) plus the period-1 hypothesis on `f`
(`f ∣[k] T = f` — Miyake's separate hypothesis, NOT inherited from `g`),
the slash identity for `f` extends from the α_l-conjugation image to all
matrices of the form `T^i · γ̃ · T^j` for `γ̃ = α_l γ α_l⁻¹` (γ ∈ Γ₀(N))
and arbitrary integer powers `i, j`:

```
f ∣[k] (T^i · γ̃ · T^j) = (χ d_γ) • f.
```

The character value is the same as in `conductor_slash_eq`: it depends
only on the (1,1)-entry of `γ`, which is preserved under both T-translation
and α_l-conjugation. -/
lemma conductor_slash_T_conj_eq (l N : ℕ) [NeZero l] [NeZero N]
    (h_dvd : l ∣ N) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f)
    (i j : ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    f ∣[k] (mapGL ℝ
        (ModularGroup.T ^ i *
          levelRaiseConjOfDvd l γ
            (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγ) *
          ModularGroup.T ^ j) : GL (Fin 2) ℝ) =
      (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) • f := by
  set gtilde := levelRaiseConjOfDvd l γ
    (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγ) with gtilde_def
  set c := (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) with c_def
  -- Step 1: distribute the mapGL over the matrix product (it's a MonoidHom).
  rw [show mapGL ℝ (ModularGroup.T ^ i * gtilde * ModularGroup.T ^ j) =
        mapGL ℝ (ModularGroup.T ^ i) * mapGL ℝ gtilde * mapGL ℝ (ModularGroup.T ^ j) from
      by simp [map_mul]]
  -- Step 2: split the slash via slash_mul (twice).
  rw [SlashAction.slash_mul, SlashAction.slash_mul]
  -- Goal: ((f ∣ T^i) ∣ γ̃) ∣ T^j = c • f
  -- Step 3: f ∣ T^i = f via period-1 extended to integer powers.
  rw [slash_T_zpow_eq_self_of_slash_T_eq k f hf_period i]
  -- Goal: (f ∣ γ̃) ∣ T^j = c • f
  -- Step 4: f ∣ γ̃ = c • f via conductor_slash_eq.
  rw [conductor_slash_eq l N h_dvd k χ f g hg_char hg_eq γ hγ]
  -- Goal: (c • f) ∣ T^j = c • f
  -- Step 5: scalar pulls through GL slash (σ trivial since det = 1),
  --         then period-1 extended.
  have hσ_T : UpperHalfPlane.σ
      (mapGL ℝ (ModularGroup.T ^ j) : GL (Fin 2) ℝ) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos]
    show (0 : ℝ) < (Matrix.GeneralLinearGroup.det
      (mapGL ℝ (ModularGroup.T ^ j))).val
    rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num
  rw [ModularForm.smul_slash, hσ_T, RingHom.id_apply,
    slash_T_zpow_eq_self_of_slash_T_eq k f hf_period j]

/-! ### Lowered slash field — full Γ₀(N/l) coverage (T046)

Combining the T044 slash bridge `conductor_slash_T_conj_eq` with the
T046 group factorisation `exists_T_levelRaiseConj_T_factor`, the slash
identity for `f` extends to ALL of `Γ₀(N/l)` (not just the α_l-image
or its T-conjugates). This is the full slash-field discharge for the
lowered modular form bundling. -/

/-- **Lowered slash field for Γ₀(N/l).** Under the T044 / T046 hypotheses
(g ∈ modFormCharSpace, ⇑g = levelRaiseFun l k f, period-1 of f, l ∣ N),
for every `γ' ∈ Γ₀(N/l)`, the slash action of `mapGL ℝ γ'` on `f`
yields a Nebentypus character value times `f`:

```
f ∣[k] mapGL ℝ γ' = (χ.toUnitHom (Gamma0MapUnits ⟨γ_lift, hγ_lift⟩) : ℂ) • f
```

where `(γ_lift, hγ_lift)` is the lifted element of `Γ₀(N)` produced by
`exists_T_levelRaiseConj_T_factor`.

Proof: extract the factorisation `γ' = T^i · γ̃ · T^j` and apply the
T044 bridge `conductor_slash_T_conj_eq`. -/
lemma conductor_slash_eq_of_mem_Gamma0_div
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f)
    (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 (N / l)) :
    ∃ (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N),
      f ∣[k] (mapGL ℝ γ' : GL (Fin 2) ℝ) =
        (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) • f := by
  obtain ⟨i, j, γ, hγ, hfact, _⟩ :=
    exists_T_levelRaiseConj_T_factor l N h_dvd γ' hγ'
  refine ⟨γ, hγ, ?_⟩
  rw [hfact]
  exact conductor_slash_T_conj_eq l N h_dvd k χ f g hg_char hg_eq hf_period i j γ hγ

/-! ### Character collapse for Γ₁(N/l) (T048)

For `δ ∈ Γ₁(N/l)`, the slash action of `mapGL ℝ δ` on `f` is the IDENTITY
(no character twist), provided `χ.FactorsThrough (N/l)` (the Case A
factor-through hypothesis).

The key observation: from the T046 factorisation
`δ = T^i · γ̃ · T^j` with `γ̃ = α_l γ α_l⁻¹` for `γ ∈ Γ₀(N)`, we get the
slash identity `f ∣[k] δ = χ(γ.val 1 1 mod N) · f`. Reducing mod `(N/l)`
(via `χ.FactorsThrough (N/l)`), the character value depends only on
`γ.val 1 1 mod (N/l)`. From the T046 factorisation,
`γ.val 1 1 = δ.val 1 1 - δ.val 1 0 * j`. Reducing mod `(N/l)`:
`δ.val 1 0 ≡ 0` (since `δ ∈ Γ₀(N/l)`), so
`γ.val 1 1 ≡ δ.val 1 1 ≡ 1 mod (N/l)` (the last by `δ ∈ Γ₁(N/l)`).
Hence `χ_low(1) = 1`, and `f ∣[k] δ = 1 · f = f`. -/

/-- **Slash invariance of `f` under `Γ₁(N/l)`.** Under the Case A
hypotheses including `χ.FactorsThrough (N/l)`, the function `f`
transforms trivially under the slash action of `mapGL ℝ δ` for every
`δ ∈ Γ₁(N/l)`. This is the "slash field" needed to bundle `f` into a
modular form at the lowered level. -/
lemma conductor_slash_eq_self_of_mem_Gamma1_div
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_fac : χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma1 (N / l)) :
    f ∣[k] (mapGL ℝ δ : GL (Fin 2) ℝ) = f := by
  have hδ_Γ₀ : δ ∈ Gamma0 (N / l) := Gamma1_in_Gamma0 _ hδ
  -- Use the strengthened factorisation that exposes γ.val 1 1.
  obtain ⟨i, j, γ, hγ, hfact, hdiag⟩ :=
    exists_T_levelRaiseConj_T_factor l N h_dvd δ hδ_Γ₀
  rw [hfact, conductor_slash_T_conj_eq l N h_dvd k χ f g hg_char hg_eq
    hf_period i j γ hγ]
  -- Goal: (χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) : ℂ) • f = f
  -- Show the character value is 1.
  suffices h_char : χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) = 1 by
    rw [h_char, Units.val_one, one_smul]
  -- Apply the loweredCharacter bridge: χ.toUnitHom factors through
  -- (loweredCharacter h_fac).toUnitHom ∘ ZMod.unitsMap _.
  rw [toUnitHom_loweredCharacter h_fac, MonoidHom.comp_apply]
  -- Need: ZMod.unitsMap h_fac.dvd (Gamma0MapUnits ⟨γ, hγ⟩) = 1.
  -- This unit is (γ.val 1 1 : ZMod N) reduced to (ZMod (N/l)).
  have h_red : ZMod.unitsMap h_fac.dvd (Gamma0MapUnits ⟨γ, hγ⟩) = 1 := by
    apply Units.ext
    simp only [Units.val_one, ZMod.unitsMap_val, Gamma0MapUnits_val]
    -- Goal: (ZMod.castHom h_fac.dvd (ZMod (N/l))) (Gamma0Map N ⟨γ, hγ⟩) = 1
    have hgmap : Gamma0Map N ⟨γ, hγ⟩ = ((γ.val 1 1 : ℤ) : ZMod N) := rfl
    rw [hgmap]
    rw [ZMod.cast_intCast h_fac.dvd]
    -- Goal: ((γ.val 1 1 : ℤ) : ZMod (N/l)) = 1
    rw [hdiag]
    push_cast
    rw [Gamma1_mem] at hδ
    obtain ⟨_, hd_one, hc_zero⟩ := hδ
    rw [hd_one, hc_zero, zero_mul, sub_zero]
  rw [h_red, map_one]

/-! ### Boundedness at `i∞` for the lowered function

The lowered function `f` (with `g(τ) = f(l·τ)`) inherits boundedness at
the cusp `i∞` from `g`: as `Im(τ) → ∞`, the substitution `τ ↦ α_l⁻¹ • τ`
sends `Im(τ)` to `Im(τ)/l`, so `f(τ) = g(α_l⁻¹ • τ)` stays bounded
because `g` is bounded at `i∞`. This is one component of the cusp
regularity needed to bundle `f` as a `ModularForm`. -/

/-- The action of `(levelRaiseMatrix l)⁻¹` on `ℍ` scales the underlying
ℂ-coordinate by `1/l`: `(α_l⁻¹ • z).coe = z.coe / l`. Derived from the
diagonal action of `α_l` (`coe_levelRaiseMatrix_smul`) by inverting
`α_l • (α_l⁻¹ • z) = z`. -/
lemma coe_levelRaiseMatrix_inv_smul (l : ℕ) [NeZero l] (z : UpperHalfPlane) :
    (((levelRaiseMatrix l)⁻¹ • z : UpperHalfPlane) : ℂ) = (↑z : ℂ) / (l : ℂ) := by
  have hl_ne : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  have h_unit : (levelRaiseMatrix l) • ((levelRaiseMatrix l)⁻¹ • z) = z := by
    rw [smul_smul, mul_inv_cancel, one_smul]
  have h_coe_eq : (((levelRaiseMatrix l) • ((levelRaiseMatrix l)⁻¹ • z) :
      UpperHalfPlane) : ℂ) = ((z : UpperHalfPlane) : ℂ) := by rw [h_unit]
  rw [coe_levelRaiseMatrix_smul] at h_coe_eq
  -- h_coe_eq : (l : ℂ) * (((α_l⁻¹ • z) : UpperHalfPlane) : ℂ) = (z : ℂ)
  rw [eq_div_iff hl_ne, mul_comm]
  exact h_coe_eq

/-- The imaginary part of `(α_l⁻¹ • z)` is `z.im / l`. -/
lemma im_levelRaiseMatrix_inv_smul (l : ℕ) [NeZero l] (z : UpperHalfPlane) :
    ((levelRaiseMatrix l)⁻¹ • z : UpperHalfPlane).im = z.im / (l : ℝ) := by
  show (((levelRaiseMatrix l)⁻¹ • z : UpperHalfPlane) : ℂ).im = z.im / (l : ℝ)
  rw [coe_levelRaiseMatrix_inv_smul]
  -- Goal: (z.coe / (l : ℂ)).im = z.im / (l : ℝ)
  rw [show (l : ℂ) = ((l : ℝ) : ℂ) from by push_cast; rfl,
    Complex.div_ofReal_im]
  rfl

/-- **Boundedness at `i∞` transfer.** If `g = levelRaiseFun l k f` and `g` is
bounded at `i∞`, then so is `f`. The proof: `f τ = g (α_l⁻¹ • τ)`
(by `fun_eq_apply_levelRaiseMatrix_inv_smul`); as `Im(τ) → ∞`,
`Im(α_l⁻¹ • τ) = Im(τ)/l → ∞`, so `g (α_l⁻¹ • τ)` stays bounded. -/
lemma isBoundedAtImInfty_of_levelRaiseFun_eq
    (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ)
    (hg_bdd : UpperHalfPlane.IsBoundedAtImInfty g)
    (hg_eq : g = levelRaiseFun l k f) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at *
  obtain ⟨M, A, hbound⟩ := hg_bdd
  have hl_pos : (0 : ℝ) < (l : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero l)
  refine ⟨M, A * (l : ℝ), fun z' hz' => ?_⟩
  rw [fun_eq_apply_levelRaiseMatrix_inv_smul l k f g hg_eq z']
  apply hbound
  rw [im_levelRaiseMatrix_inv_smul]
  rw [le_div_iff₀ hl_pos]
  exact hz'

/-! ### Slash equation toward all-cusp boundedness reduction

For the lowered modular form bundling, `bdd_at_cusps' f` requires
`IsBoundedAtImInfty (f ∣[k] mapGL ℝ A)` for every `A : SL(2, ℤ)`
(via `ModularFormClass.bdd_at_infty_slash`). The key reduction:
`f ∣[k] A` is a constant scalar multiple of `g ∣[k] (α_l⁻¹ * mapGL ℝ A)`,
so its boundedness reduces to that of the latter. -/

/-- The conjugation factor `σ` for `(levelRaiseMatrix l)⁻¹` is the
identity (positive determinant `1/l`). -/
lemma σ_levelRaiseMatrix_inv (l : ℕ) [NeZero l] :
    UpperHalfPlane.σ ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) = RingHom.id ℂ := by
  unfold UpperHalfPlane.σ
  rw [if_pos (levelRaiseMatrix_inv_det_pos l)]

/-- **Inverse-slash equation**: `g ∣[k] α_l⁻¹ = (l^(1-k)) • f`.

Direct slash-composition from `g = levelRaiseFun l k f`:
`g ∣[k] α_l⁻¹ = ((l^(1-k)) • (f ∣[k] α_l)) ∣[k] α_l⁻¹
            = (l^(1-k)) • (f ∣[k] (α_l * α_l⁻¹))
            = (l^(1-k)) • (f ∣[k] 1) = (l^(1-k)) • f`.
The scalar pulls through `α_l⁻¹`-slash because `σ α_l⁻¹ = id`. -/
lemma slash_inv_eq_smul_of_levelRaiseFun_eq (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ) (hg_eq : g = levelRaiseFun l k f) :
    g ∣[k] ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) = ((l : ℂ) ^ (1 - k)) • f := by
  rw [hg_eq]
  show (((l : ℂ) ^ (1 - k)) • (f ∣[k] (levelRaiseMatrix l : GL (Fin 2) ℝ))) ∣[k]
      ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) = ((l : ℂ) ^ (1 - k)) • f
  rw [ModularForm.smul_slash, σ_levelRaiseMatrix_inv, RingHom.id_apply,
    ← SlashAction.slash_mul]
  rw [show (levelRaiseMatrix l : GL (Fin 2) ℝ) * (levelRaiseMatrix l)⁻¹ = 1
    from mul_inv_cancel _]
  rw [SlashAction.slash_one]

/-- **Slash-by-SL reduction.** For any `A : SL(2, ℤ)`,
```
f ∣[k] mapGL ℝ A = (l^(k-1)) • g ∣[k] ((levelRaiseMatrix l)⁻¹ * mapGL ℝ A).
```
Combines `slash_inv_eq_smul_of_levelRaiseFun_eq` (the key inverse-slash
equation) with `slash_mul` (slash composition), inverting the scalar
factor on the way. -/
lemma slash_eq_of_levelRaiseFun_eq (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ) (hg_eq : g = levelRaiseFun l k f)
    (A : SL(2, ℤ)) :
    f ∣[k] (mapGL ℝ A : GL (Fin 2) ℝ) =
      ((l : ℂ) ^ (k - 1)) •
        (g ∣[k] (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) *
          (mapGL ℝ A : GL (Fin 2) ℝ))) := by
  -- From the inverse-slash equation, f = (l^(k-1)) • (g ∣[k] α_l⁻¹).
  have hf_eq : f = ((l : ℂ) ^ (k - 1)) •
      (g ∣[k] ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ)) := by
    rw [slash_inv_eq_smul_of_levelRaiseFun_eq l k f g hg_eq]
    have hl_ne : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
    rw [smul_smul, ← zpow_add₀ hl_ne, show k - 1 + (1 - k) = 0 from by ring,
      zpow_zero, one_smul]
  conv_lhs => rw [hf_eq]
  -- Distribute scalar through the GL-slash (σ is id for det = 1).
  have hσA : UpperHalfPlane.σ (mapGL ℝ A : GL (Fin 2) ℝ) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos]
    show (0 : ℝ) < (Matrix.GeneralLinearGroup.det (mapGL ℝ A)).val
    rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num
  rw [ModularForm.smul_slash, hσA, RingHom.id_apply, ← SlashAction.slash_mul]

/-- **Slash-boundedness reduction.** For any `A : SL(2, ℤ)`, the
boundedness of `f ∣[k] mapGL ℝ A` at `i∞` is equivalent to the
boundedness of `g ∣[k] (α_l⁻¹ * mapGL ℝ A)` at `i∞`. -/
lemma isBoundedAtImInfty_slash_iff_levelRaiseFun_eq
    (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ) (hg_eq : g = levelRaiseFun l k f)
    (A : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty
        (f ∣[k] (mapGL ℝ A : GL (Fin 2) ℝ)) ↔
      UpperHalfPlane.IsBoundedAtImInfty
        (g ∣[k] (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) *
          (mapGL ℝ A : GL (Fin 2) ℝ))) := by
  rw [slash_eq_of_levelRaiseFun_eq l k f g hg_eq A]
  -- Goal: IsBoundedAtImInfty ((c • h)) ↔ IsBoundedAtImInfty h, with c ≠ 0.
  have hc_ne : ((l : ℂ) ^ (k - 1)) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne l))
  rw [UpperHalfPlane.isBoundedAtImInfty_iff, UpperHalfPlane.isBoundedAtImInfty_iff]
  constructor
  · rintro ⟨M, A_im, hbound⟩
    refine ⟨M / ‖((l : ℂ) ^ (k - 1))‖, A_im, fun τ hτ => ?_⟩
    have h := hbound τ hτ
    rw [Pi.smul_apply, smul_eq_mul, norm_mul] at h
    rwa [le_div_iff₀ (by rw [norm_pos_iff]; exact hc_ne), mul_comm]
  · rintro ⟨M, A_im, hbound⟩
    refine ⟨‖((l : ℂ) ^ (k - 1))‖ * M, A_im, fun τ hτ => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound τ hτ) (norm_nonneg _)

/-! ### All-cusp boundedness for the lowered form (T059)

Using the slash-boundedness reduction `isBoundedAtImInfty_slash_iff_levelRaiseFun_eq`
together with the structural cusp condition on `g` (via `bdd_at_cusps'`), we obtain
`IsBoundedAtImInfty (f ∣[k] mapGL ℝ A)` for every `A : SL(2, ℤ)`. From this, the
all-cusp regularity follows for the candidate lower-level form `f`, discharging
the `bdd_at_cusps'` field at every cusp of `(Gamma1 (N/l)).map (mapGL ℝ)`. -/

open OnePoint in
/-- The matrix entry at position `(1, 0)` of `(levelRaiseMatrix l)⁻¹` is `0`. -/
private lemma levelRaiseMatrix_inv_apply_one_zero (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 1 0 = 0 := by
  have h_unit : (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l) : ℝ) = (l : ℝ) := by
    simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]
  have hl_ne : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  show ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val 1 0 = 0
  rw [Matrix.GeneralLinearGroup.coe_inv]
  show (((levelRaiseMatrix l : GL (Fin 2) ℝ)).val)⁻¹ 1 0 = 0
  rw [Matrix.inv_def]
  show (Ring.inverse ((levelRaiseMatrix l : GL (Fin 2) ℝ).val).det •
      ((levelRaiseMatrix l : GL (Fin 2) ℝ).val).adjugate) 1 0 = 0
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

open OnePoint in
/-- The matrix entry at position `(1, 1)` of `(levelRaiseMatrix l)⁻¹` is `1`. -/
private lemma levelRaiseMatrix_inv_apply_one_one (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 1 1 = 1 := by
  show ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val 1 1 = 1
  rw [Matrix.GeneralLinearGroup.coe_inv]
  rw [Matrix.inv_def]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

open OnePoint in
/-- The matrix entry at position `(0, 0)` of `(levelRaiseMatrix l)⁻¹` is `1/l`. -/
private lemma levelRaiseMatrix_inv_apply_zero_zero (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 0 0 = (l : ℝ)⁻¹ := by
  show ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val 0 0 = (l : ℝ)⁻¹
  rw [Matrix.GeneralLinearGroup.coe_inv]
  rw [Matrix.inv_def]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

open OnePoint in
/-- The matrix entry at position `(0, 1)` of `(levelRaiseMatrix l)⁻¹` is `0`. -/
private lemma levelRaiseMatrix_inv_apply_zero_one (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 0 1 = 0 := by
  show ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val 0 1 = 0
  rw [Matrix.GeneralLinearGroup.coe_inv]
  rw [Matrix.inv_def]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

/-- The (1, 0) entry of `(levelRaiseMatrix l)⁻¹ * mapGL ℝ A` is `(A.val 1 0 : ℝ)`. -/
private lemma levelRaiseMatrix_inv_mul_mapGL_apply_one_zero
    (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) 1 0 =
      (A.val 1 0 : ℝ) := by
  show (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)).val 1 0 = _
  rw [Units.val_mul]
  show (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val *
      (mapGL ℝ A : GL (Fin 2) ℝ).val) 1 0 = (A.val 1 0 : ℝ)
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  show ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 1 0 * (mapGL ℝ A : GL (Fin 2) ℝ) 0 0 +
      ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 1 1 * (mapGL ℝ A : GL (Fin 2) ℝ) 1 0 =
        (A.val 1 0 : ℝ)
  rw [levelRaiseMatrix_inv_apply_one_zero, levelRaiseMatrix_inv_apply_one_one,
    zero_mul, one_mul, zero_add]
  show ((mapGL ℝ A : GL (Fin 2) ℝ).val) 1 0 = (A.val 1 0 : ℝ)
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- The (0, 0) entry of `(levelRaiseMatrix l)⁻¹ * mapGL ℝ A` is `(A.val 0 0 : ℝ) / l`. -/
private lemma levelRaiseMatrix_inv_mul_mapGL_apply_zero_zero
    (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) 0 0 =
      (A.val 0 0 : ℝ) / (l : ℝ) := by
  show (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)).val 0 0 = _
  rw [Units.val_mul]
  show (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val *
      (mapGL ℝ A : GL (Fin 2) ℝ).val) 0 0 = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  show ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 0 0 * (mapGL ℝ A : GL (Fin 2) ℝ) 0 0 +
      ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 0 1 * (mapGL ℝ A : GL (Fin 2) ℝ) 1 0 =
        (A.val 0 0 : ℝ) / (l : ℝ)
  rw [levelRaiseMatrix_inv_apply_zero_zero, levelRaiseMatrix_inv_apply_zero_one,
    zero_mul, add_zero]
  show (l : ℝ)⁻¹ * (mapGL ℝ A : GL (Fin 2) ℝ) 0 0 = (A.val 0 0 : ℝ) / (l : ℝ)
  rw [show ((mapGL ℝ A : GL (Fin 2) ℝ)) 0 0 = (A.val 0 0 : ℝ) from by
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]]
  ring

/-- Helper: the gcd `gcd (A.val 0 0) (l * A.val 1 0)` is non-zero, since the first
column of `A : SL(2, ℤ)` is non-zero (det A = 1) and `l ≠ 0`. -/
private lemma gcd_levelRaise_first_col_ne_zero (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0) : ℤ) ≠ 0 := by
  intro hgcd
  rw [gcd_eq_zero_iff] at hgcd
  obtain ⟨ha, hlc⟩ := hgcd
  have hl_ne : (l : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  rcases mul_eq_zero.mp hlc with h | h
  · exact hl_ne h
  · have hdet : A.val.det = 1 := A.property
    rw [Matrix.det_fin_two, ha, h] at hdet
    norm_num at hdet

/-- The `SL(2, ℤ)` cusp witness whose `mapGL ℝ`-image acts on `∞` to give the same
point as `(α_l)⁻¹ * mapGL ℝ A`. Constructed via `IsCoprime.exists_SL2_col` from the
primitive form of `(A.val 0 0, l * A.val 1 0)`. -/
noncomputable def cuspWitnessLevelRaiseInv (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    SL(2, ℤ) :=
  Classical.choose <|
    (isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
      (gcd_levelRaise_first_col_ne_zero l A)).exists_SL2_col 0

/-- The first column of the cusp witness:
`(B 0 0, B 1 0) = (A.val 0 0 / d, l * A.val 1 0 / d)` where `d = gcd(...)`. -/
private lemma cuspWitnessLevelRaiseInv_first_col (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (cuspWitnessLevelRaiseInv l A) 0 0 =
        A.val 0 0 / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) ∧
    (cuspWitnessLevelRaiseInv l A) 1 0 =
        ((l : ℤ) * A.val 1 0) / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) :=
  Classical.choose_spec
    ((isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
      (gcd_levelRaise_first_col_ne_zero l A)).exists_SL2_col 0)

/-- The matrix entry `(mapGL ℝ B).val 1 0` of the level-raise cusp witness equals
`(l * A.val 1 0 / d : ℤ : ℝ)` where `d = gcd(A.val 0 0, l * A.val 1 0)`. -/
private lemma mapGL_cuspWitnessLevelRaiseInv_apply_one_zero
    (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ) 1 0 =
      ((((l : ℤ) * A.val 1 0) / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) : ℤ) : ℝ) := by
  show (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ).val 1 0 = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  show (algebraMap ℤ ℝ) ((cuspWitnessLevelRaiseInv l A).val 1 0) = _
  rw [(cuspWitnessLevelRaiseInv_first_col l A).2]
  simp

/-- The matrix entry `(mapGL ℝ B).val 0 0` of the level-raise cusp witness equals
`(A.val 0 0 / d : ℤ : ℝ)` where `d = gcd(A.val 0 0, l * A.val 1 0)`. -/
private lemma mapGL_cuspWitnessLevelRaiseInv_apply_zero_zero
    (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ) 0 0 =
      ((A.val 0 0 / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) : ℤ) : ℝ) := by
  show (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ).val 0 0 = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  show (algebraMap ℤ ℝ) ((cuspWitnessLevelRaiseInv l A).val 0 0) = _
  rw [(cuspWitnessLevelRaiseInv_first_col l A).1]
  simp

open OnePoint in
/-- **Cusp equality.** The `mapGL ℝ`-image of `cuspWitnessLevelRaiseInv l A` and the
matrix `(α_l)⁻¹ * mapGL ℝ A` send `∞` to the same point of `OnePoint ℝ`. -/
private lemma mapGL_cuspWitnessLevelRaiseInv_smul_infty_eq
    (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ) =
      (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) • ∞ := by
  set d : ℤ := gcd (A.val 0 0) ((l : ℤ) * A.val 1 0) with hd_def
  have hd_ne : d ≠ 0 := gcd_levelRaise_first_col_ne_zero l A
  have hd_dvd_a : d ∣ A.val 0 0 := gcd_dvd_left _ _
  have hd_dvd_lc : d ∣ ((l : ℤ) * A.val 1 0) := gcd_dvd_right _ _
  have hl_ne_int : (l : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  have hl_ne_real : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  have hd_real_ne : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd_ne
  -- Rewrite both sides using smul_infty_eq_ite.
  rw [OnePoint.smul_infty_eq_ite, OnePoint.smul_infty_eq_ite]
  rw [mapGL_cuspWitnessLevelRaiseInv_apply_one_zero,
    mapGL_cuspWitnessLevelRaiseInv_apply_zero_zero,
    levelRaiseMatrix_inv_mul_mapGL_apply_one_zero,
    levelRaiseMatrix_inv_mul_mapGL_apply_zero_zero]
  -- Goal: if cast(γ) = 0 then ∞ else cast(α)/cast(γ) = if cast(c) = 0 then ∞ else cast(a)/(l*cast(c))
  -- Where α = a/d, γ = l*c/d, a = A.val 0 0, c = A.val 1 0.
  -- Both ite conditions: cast(γ) = 0 ↔ γ = 0 ↔ l*c = 0 (since d ≠ 0) ↔ c = 0.
  have h_int_div_a : (((A.val 0 0) / d : ℤ) : ℝ) = (A.val 0 0 : ℝ) / (d : ℝ) :=
    Int.cast_div hd_dvd_a hd_real_ne
  have h_int_div_lc : ((((l : ℤ) * A.val 1 0) / d : ℤ) : ℝ) =
      ((l : ℝ) * A.val 1 0) / (d : ℝ) := by
    rw [Int.cast_div hd_dvd_lc hd_real_ne]; push_cast; ring
  rw [h_int_div_a, h_int_div_lc]
  -- Goal: if (l*c/d : ℝ) = 0 then ∞ else (a/d) / (l*c/d) =
  --       if (c : ℝ) = 0 then ∞ else (a/l) / c
  by_cases hc : (A.val 1 0 : ℝ) = 0
  · -- Case c = 0: both ite branches go to ∞.
    have h_lc_zero : ((l : ℝ) * (A.val 1 0 : ℝ)) / (d : ℝ) = 0 := by
      rw [hc, mul_zero, zero_div]
    rw [if_pos h_lc_zero, if_pos hc]
  · -- Case c ≠ 0:
    have h_lc_ne : ((l : ℝ) * (A.val 1 0 : ℝ)) / (d : ℝ) ≠ 0 :=
      div_ne_zero (mul_ne_zero hl_ne_real hc) hd_real_ne
    rw [if_neg h_lc_ne, if_neg hc]
    -- Goal: ((a:ℝ)/d) / ((l:ℝ)*c/d) = ((a:ℝ)/l) / c
    field_simp

open OnePoint in
/-- **IsCusp transfer.** The cusp `(α_l⁻¹ * mapGL ℝ A) • ∞` is a cusp of any
arithmetic subgroup `Γ : Subgroup (GL (Fin 2) ℝ)`. Specifically, it is the
image under `mapGL ℝ` of `cuspWitnessLevelRaiseInv l A : SL(2, ℤ)` acting on `∞`,
hence rational, hence a cusp of `𝒮ℒ` (and therefore of every arithmetic subgroup
by `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`). -/
lemma isCusp_levelRaiseMatrix_inv_mul_mapGL_smul_infty
    (l : ℕ) [NeZero l] (A : SL(2, ℤ))
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] :
    IsCusp ((((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) *
      (mapGL ℝ A : GL (Fin 2) ℝ)) • ∞) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']
  exact ⟨cuspWitnessLevelRaiseInv l A,
    (mapGL_cuspWitnessLevelRaiseInv_smul_infty_eq l A).symm⟩

open OnePoint in
/-- **Boundedness of `g ∣[k] (α_l⁻¹ * mapGL ℝ A)` at `i∞`.** Direct application of
the structural cusp condition `bdd_at_cusps'` of `g` at the cusp
`(α_l⁻¹ * mapGL ℝ A) • ∞`. -/
lemma isBoundedAtImInfty_slash_levelRaiseMatrix_inv_mul_mapGL
    (l N : ℕ) [NeZero l] [NeZero N] (k : ℤ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty
      (⇑g ∣[k] (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) *
        (mapGL ℝ A : GL (Fin 2) ℝ))) := by
  have hc := isCusp_levelRaiseMatrix_inv_mul_mapGL_smul_infty l A
    ((Gamma1 N).map (mapGL ℝ))
  exact ModularFormClass.bdd_at_cusps g hc _ rfl

/-- **All-cusp boundedness for `f` at every SL(2, ℤ) translate.** Combining the
reduction `isBoundedAtImInfty_slash_iff_levelRaiseFun_eq` with the structural
cusp condition on `g`, we obtain `IsBoundedAtImInfty (f ∣[k] mapGL ℝ A)` for
every `A : SL(2, ℤ)`. -/
lemma isBoundedAtImInfty_slash_mapGL_of_levelRaiseFun_eq
    (l N : ℕ) [NeZero l] [NeZero N] (k : ℤ)
    (f : UpperHalfPlane → ℂ) (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_eq : ⇑g = levelRaiseFun l k f) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (f ∣[k] (mapGL ℝ A : GL (Fin 2) ℝ)) := by
  rw [isBoundedAtImInfty_slash_iff_levelRaiseFun_eq l k f ⇑g hg_eq A]
  exact isBoundedAtImInfty_slash_levelRaiseMatrix_inv_mul_mapGL l N k g A

open OnePoint in
/-- **All-cusp boundedness theorem (T059).** The candidate lower-level form `f`
is bounded at every cusp of the lowered congruence subgroup
`(Gamma1 (N/l)).map (mapGL ℝ)`. This is the slash-action version of
`bdd_at_cusps' f`. -/
theorem bdd_at_cusps_of_levelRaiseFun_eq
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (f : UpperHalfPlane → ℂ) (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 (N / l)).map (mapGL ℝ))) :
    OnePoint.IsBoundedAt c f k := by
  -- Need NeZero (N / l) for the IsArithmetic instance on the lowered subgroup.
  haveI : NeZero (N / l) := ⟨by
    have hl_pos : 0 < l := Nat.pos_of_neZero l
    have hN_pos : 0 < N := Nat.pos_of_neZero N
    exact (Nat.div_pos (Nat.le_of_dvd hN_pos h_dvd) hl_pos).ne'⟩
  -- Use IsArithmetic to reduce to IsCusp c 𝒮ℒ.
  have hc_SL : IsCusp c 𝒮ℒ :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
  -- Use isBoundedAt_iff_exists_SL2Z: provide one SL(2, ℤ) witness γ + bdd at γ.
  rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc_SL]
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc_SL
  refine ⟨γ, hγ.symm, ?_⟩
  -- Goal: IsBoundedAtImInfty (f ∣[k] γ) where slash is via SL2Z action.
  rw [ModularForm.SL_slash]
  -- Goal: IsBoundedAtImInfty (f ∣[k] (γ : GL (Fin 2) ℝ))
  exact isBoundedAtImInfty_slash_mapGL_of_levelRaiseFun_eq l N k f g hg_eq γ

/-! ### Lowered ModularForm bundling (T059)

Combining all four structural fields — slash invariance from
`conductor_slash_eq_self_of_mem_Gamma1_div`, holomorphy from
`mdifferentiable_of_modularForm_levelRaiseFun_eq`, and cusp regularity
from `bdd_at_cusps_of_levelRaiseFun_eq` — yields the **lowered Case A
modular form** at level `Γ₁(N/l)`. This is the structural bundle the
conductor-lowering theorem produces. -/

/-- **Case A lowered modular form bundle.** Given the Case A hypotheses
(level `N`, divisibility `l ∣ N`, character `χ` factoring through `N/l`,
underlying function relation `⇑g = levelRaiseFun l k f`, and the period-1
hypothesis `f ∣[k] T = f`), the candidate function `f` bundles into a
`ModularForm` at the lowered level `(Gamma1 (N/l)).map (mapGL ℝ)`. -/
noncomputable def conductorTheoremCaseA_modularForm
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_fac : χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ) (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    ModularForm ((Gamma1 (N / l)).map (mapGL ℝ)) k where
  toFun := f
  slash_action_eq' γ hγ_mem := by
    obtain ⟨δ, hδ_mem, hδ_eq⟩ := Subgroup.mem_map.mp hγ_mem
    rw [← hδ_eq]
    exact conductor_slash_eq_self_of_mem_Gamma1_div l N h_dvd k χ h_fac f g hg_char hg_eq
      hf_period δ hδ_mem
  holo' := mdifferentiable_of_modularForm_levelRaiseFun_eq l k f g hg_eq
  bdd_at_cusps' hc := bdd_at_cusps_of_levelRaiseFun_eq l N h_dvd k f g hg_eq hc

/-- The bundled `conductorTheoremCaseA_modularForm` has underlying function `f`. -/
@[simp]
lemma conductorTheoremCaseA_modularForm_apply
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_fac : χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ) (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    ⇑(conductorTheoremCaseA_modularForm l N h_dvd k χ h_fac f g hg_char hg_eq hf_period) = f :=
  rfl

/-! ### CuspForm version of Case A (T064)

Mirror of the T048/T059 boundedness pipeline using `IsZeroAtImInfty` and
`OnePoint.IsZeroAt` in place of `IsBoundedAtImInfty` and
`OnePoint.IsBoundedAt`. The structure of the proofs is identical to the
ModularForm version: the slash-by-SL reduction is the same scalar
identity (`slash_eq_of_levelRaiseFun_eq`), and the cusp identification
machinery (`cuspWitnessLevelRaiseInv`, etc.) is shared. The only change
is that we use `g.zero_at_cusps'` (for `g : CuspForm`) rather than
`g.bdd_at_cusps'`.

This gives the **lowered Case A cusp form** at level `Γ₁(N/l)`, which
is the typical target in Miyake §4.6.4 (whose statement is for cusp
forms specifically). -/

/-- **Inverse zero-at-i∞ transfer.** If `g = levelRaiseFun l k f` and `g`
is zero at `i∞`, then so is `f`. The proof: `f τ = g (α_l⁻¹ • τ)`
(by `fun_eq_apply_levelRaiseMatrix_inv_smul`); as `Im(τ) → ∞`,
`Im(α_l⁻¹ • τ) = Im(τ)/l → ∞`, so `g (α_l⁻¹ • τ) → 0`. -/
lemma isZeroAtImInfty_of_levelRaiseFun_eq
    (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ)
    (hg_zero : UpperHalfPlane.IsZeroAtImInfty g)
    (hg_eq : g = levelRaiseFun l k f) :
    UpperHalfPlane.IsZeroAtImInfty f := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at *
  intro ε hε
  obtain ⟨A, hbound⟩ := hg_zero ε hε
  have hl_pos : (0 : ℝ) < (l : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero l)
  refine ⟨A * (l : ℝ), fun z' hz' => ?_⟩
  rw [fun_eq_apply_levelRaiseMatrix_inv_smul l k f g hg_eq z']
  apply hbound
  rw [im_levelRaiseMatrix_inv_smul]
  rw [le_div_iff₀ hl_pos]
  exact hz'

/-- **Slash zero-at-i∞ reduction.** For any `A : SL(2, ℤ)`, the
zero-at-`i∞` of `f ∣[k] mapGL ℝ A` is equivalent to the
zero-at-`i∞` of `g ∣[k] (α_l⁻¹ * mapGL ℝ A)`. -/
lemma isZeroAtImInfty_slash_iff_levelRaiseFun_eq
    (l : ℕ) [NeZero l] (k : ℤ)
    (f g : UpperHalfPlane → ℂ) (hg_eq : g = levelRaiseFun l k f)
    (A : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty
        (f ∣[k] (mapGL ℝ A : GL (Fin 2) ℝ)) ↔
      UpperHalfPlane.IsZeroAtImInfty
        (g ∣[k] (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) *
          (mapGL ℝ A : GL (Fin 2) ℝ))) := by
  rw [slash_eq_of_levelRaiseFun_eq l k f g hg_eq A]
  -- Goal: IsZeroAtImInfty ((c • h)) ↔ IsZeroAtImInfty h, with c ≠ 0.
  have hc_ne : ((l : ℂ) ^ (k - 1)) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne l))
  have hc_norm_pos : 0 < ‖((l : ℂ) ^ (k - 1))‖ := by
    rw [norm_pos_iff]; exact hc_ne
  rw [UpperHalfPlane.isZeroAtImInfty_iff, UpperHalfPlane.isZeroAtImInfty_iff]
  constructor
  · intro h ε hε
    obtain ⟨A_im, hbound⟩ := h (ε * ‖((l : ℂ) ^ (k - 1))‖)
      (mul_pos hε hc_norm_pos)
    refine ⟨A_im, fun τ hτ => ?_⟩
    have h := hbound τ hτ
    rw [Pi.smul_apply, smul_eq_mul, norm_mul] at h
    rwa [mul_comm, ← le_div_iff₀ hc_norm_pos,
      mul_div_assoc, div_self hc_norm_pos.ne', mul_one] at h
  · intro h ε hε
    obtain ⟨A_im, hbound⟩ := h (ε / ‖((l : ℂ) ^ (k - 1))‖)
      (div_pos hε hc_norm_pos)
    refine ⟨A_im, fun τ hτ => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    have h := hbound τ hτ
    rwa [le_div_iff₀ hc_norm_pos, mul_comm] at h

open OnePoint in
/-- **Zero-at-i∞ of `g ∣[k] (α_l⁻¹ * mapGL ℝ A)`.** Direct application of the
structural cusp condition `zero_at_cusps'` of `g : CuspForm` at the cusp
`(α_l⁻¹ * mapGL ℝ A) • ∞`. -/
lemma isZeroAtImInfty_slash_levelRaiseMatrix_inv_mul_mapGL
    (l N : ℕ) [NeZero l] [NeZero N] (k : ℤ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty
      (⇑g ∣[k] (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) *
        (mapGL ℝ A : GL (Fin 2) ℝ))) := by
  have hc := isCusp_levelRaiseMatrix_inv_mul_mapGL_smul_infty l A
    ((Gamma1 N).map (mapGL ℝ))
  exact CuspFormClass.zero_at_cusps g hc _ rfl

/-- **All-SL2 zero-at-i∞ for `f`.** Combining the reduction
`isZeroAtImInfty_slash_iff_levelRaiseFun_eq` with the structural cusp
condition on `g`, we obtain `IsZeroAtImInfty (f ∣[k] mapGL ℝ A)` for
every `A : SL(2, ℤ)`. -/
lemma isZeroAtImInfty_slash_mapGL_of_levelRaiseFun_eq
    (l N : ℕ) [NeZero l] [NeZero N] (k : ℤ)
    (f : UpperHalfPlane → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_eq : ⇑g = levelRaiseFun l k f) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (f ∣[k] (mapGL ℝ A : GL (Fin 2) ℝ)) := by
  rw [isZeroAtImInfty_slash_iff_levelRaiseFun_eq l k f ⇑g hg_eq A]
  exact isZeroAtImInfty_slash_levelRaiseMatrix_inv_mul_mapGL l N k g A

open OnePoint in
/-- **All-cusp vanishing theorem (T064).** The candidate lower-level form `f`
vanishes at every cusp of the lowered congruence subgroup
`(Gamma1 (N/l)).map (mapGL ℝ)`. This is the slash-action version of
`zero_at_cusps' f`. -/
theorem zero_at_cusps_of_levelRaiseFun_eq
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (f : UpperHalfPlane → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 (N / l)).map (mapGL ℝ))) :
    OnePoint.IsZeroAt c f k := by
  haveI : NeZero (N / l) := ⟨by
    have hl_pos : 0 < l := Nat.pos_of_neZero l
    have hN_pos : 0 < N := Nat.pos_of_neZero N
    exact (Nat.div_pos (Nat.le_of_dvd hN_pos h_dvd) hl_pos).ne'⟩
  have hc_SL : IsCusp c 𝒮ℒ :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
  rw [OnePoint.isZeroAt_iff_exists_SL2Z hc_SL]
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc_SL
  refine ⟨γ, hγ.symm, ?_⟩
  rw [ModularForm.SL_slash]
  exact isZeroAtImInfty_slash_mapGL_of_levelRaiseFun_eq l N k f g hg_eq γ

/-- **Local `CuspForm.toModularForm'` upgrade.** A cusp form is canonically a
modular form via the inclusion `c.IsZeroAt → c.IsBoundedAt`. Defined locally
to avoid pulling the heavy `AdjointTheory` chain. -/
def cuspFormToModularForm {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (g : CuspForm Γ k) : ModularForm Γ k where
  toFun := g.toFun
  slash_action_eq' := g.slash_action_eq'
  holo' := g.holo'
  bdd_at_cusps' hc := fun M hM =>
    (g.zero_at_cusps' hc M hM).isBoundedAtImInfty

@[simp]
lemma cuspFormToModularForm_coe {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (g : CuspForm Γ k) : ⇑(cuspFormToModularForm g) = ⇑g := rfl

/-- A cusp form lies in the modular-form Nebentypus eigenspace iff it lies in
the cusp-form Nebentypus eigenspace, since both unfold to the same Nebentypus
slash identity via `*_iff_nebentypus`. -/
lemma cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
    {N : ℕ} [NeZero N] (k : ℤ) (χ₀ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    cuspFormToModularForm g ∈ modFormCharSpace k χ₀ ↔
      g ∈ cuspFormCharSpace k χ₀ := by
  rw [modFormCharSpace_iff_nebentypus, cuspFormCharSpace_iff_nebentypus]
  simp [cuspFormToModularForm_coe]

/-- **Case A lowered cusp form bundle.** Given the Case A hypotheses
(level `N`, divisibility `l ∣ N`, character `χ` factoring through `N/l`,
underlying function relation `⇑g = levelRaiseFun l k f` for some
`g : CuspForm`, the Nebentypus character condition `g ∈ cuspFormCharSpace`,
and the period-1 hypothesis `f ∣[k] T = f`), the candidate function `f`
bundles into a `CuspForm` at the lowered level `(Gamma1 (N/l)).map (mapGL ℝ)`. -/
noncomputable def conductorTheoremCaseA_cuspForm
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_fac : χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    CuspForm ((Gamma1 (N / l)).map (mapGL ℝ)) k where
  toFun := f
  slash_action_eq' γ hγ_mem := by
    obtain ⟨δ, hδ_mem, hδ_eq⟩ := Subgroup.mem_map.mp hγ_mem
    rw [← hδ_eq]
    have hg_mod_char : cuspFormToModularForm g ∈ modFormCharSpace k χ.toUnitHom :=
      (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        k χ.toUnitHom g).mpr hg_char
    exact conductor_slash_eq_self_of_mem_Gamma1_div l N h_dvd k χ h_fac f
      (cuspFormToModularForm g) hg_mod_char hg_eq hf_period δ hδ_mem
  holo' := mdifferentiable_of_levelRaiseFun_eq l k f ⇑g (CuspFormClass.holo g) hg_eq
  zero_at_cusps' hc := zero_at_cusps_of_levelRaiseFun_eq l N h_dvd k f g hg_eq hc

/-- The bundled `conductorTheoremCaseA_cuspForm` has underlying function `f`. -/
@[simp]
lemma conductorTheoremCaseA_cuspForm_apply
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_fac : χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    ⇑(conductorTheoremCaseA_cuspForm l N h_dvd k χ h_fac f g hg_char hg_eq hf_period) = f :=
  rfl

/-! ### Case B (vanishing) preparation (T065)

When `χ` does NOT factor through `N/l` (equivalently, `l * χ.conductor ∤ N`),
the candidate lower-level form `f` MUST vanish. This section provides the
structural ingredients for the Miyake §4.6.4 Case B argument:

1. **Unit extraction**: from `¬ χ.FactorsThrough (N/l)`, obtain
   `u : (ZMod N)ˣ` in the kernel of `ZMod.unitsMap (N/l ∣ N)` with
   `χ.toUnitHom u ≠ 1`.
2. **Lift**: lift `u` to `γ_u ∈ Γ₀(N)` via `Gamma0MapUnits_surjective`.
3. **Structural ascent** `levelRaiseConjOfDvd_mem_Gamma1_div_of_mem_ker`:
   for `γ ∈ Γ₀(N)` with `γ.val 1 1 ≡ 1 mod (N/l)`,
   `levelRaiseConjOfDvd l γ : SL(2, ℤ)` lies in `Γ₁(N/l)`.
4. **Combined slash relation**
   `case_B_slash_relation`: produces a witness `(δ, c)` with
   `δ ∈ Γ₁(N/l)`, `c ≠ 1`, and `f ∣[k] mapGL ℝ δ = c • f`.

The downstream Case B vanishing `f = 0` is closed by T072 via the
constructive two-multiplier route — see
`conductorTheoremCaseB_vanishing`. -/

/-- **Unit extraction from `¬ FactorsThrough`.** If `χ : DirichletCharacter ℂ N`
does not factor through level `d`, there is a unit `u : (ZMod N)ˣ` with
`ZMod.unitsMap hd u = 1` (i.e., `u` reduces to `1` modulo `d`) and
`χ.toUnitHom u ≠ 1`. -/
lemma exists_unit_of_not_factorsThrough
    {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    {χ : DirichletCharacter ℂ N} (h_not_fac : ¬ χ.FactorsThrough d) :
    ∃ u : (ZMod N)ˣ, ZMod.unitsMap hd u = 1 ∧ χ.toUnitHom u ≠ 1 := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd] at h_not_fac
  obtain ⟨u, hu_ker, hu_chi⟩ := SetLike.not_le_iff_exists.mp h_not_fac
  refine ⟨u, ?_, ?_⟩
  · rwa [MonoidHom.mem_ker] at hu_ker
  · intro h
    apply hu_chi
    rw [MonoidHom.mem_ker]
    exact h

/-- **Structural ascent**: if `γ ∈ Γ₀(N)` has `γ.val 1 1 ≡ 1 mod (N/l)`
(i.e., `Gamma0MapUnits ⟨γ, hγ⟩` lies in the kernel of the unit-group
reduction `(ZMod N)ˣ → (ZMod (N/l))ˣ`), then `levelRaiseConjOfDvd l γ`
lies in the smaller subgroup `Γ₁(N/l)`. -/
lemma levelRaiseConjOfDvd_mem_Gamma1_div_of_mem_ker
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N)
    (hγ_ker : ((γ.val 1 1 : ℤ) : ZMod (N / l)) = 1) :
    levelRaiseConjOfDvd l γ
      (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγ) ∈ Gamma1 (N / l) := by
  set gtilde := levelRaiseConjOfDvd l γ
    (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγ)
  have hgtilde_eq00 : gtilde.val 0 0 = γ.val 0 0 := by
    show (Matrix.of !![γ.val 0 0, l * γ.val 0 1; γ.val 1 0 / l, γ.val 1 1]) 0 0 =
      γ.val 0 0
    simp
  have hgtilde_eq11 : gtilde.val 1 1 = γ.val 1 1 := by
    show (Matrix.of !![γ.val 0 0, l * γ.val 0 1; γ.val 1 0 / l, γ.val 1 1]) 1 1 =
      γ.val 1 1
    simp
  have hgtilde_eq10 : gtilde.val 1 0 = γ.val 1 0 / (l : ℤ) := by
    show (Matrix.of !![γ.val 0 0, l * γ.val 0 1; γ.val 1 0 / l, γ.val 1 1]) 1 0 =
      γ.val 1 0 / l
    simp
  -- Common: γ ∈ Γ₀(N) ⟹ N | γ.val 1 0. Combined with l ∣ N: N/l | γ.val 1 0.
  have hN_dvd_c : (N : ℤ) ∣ γ.val 1 0 := by
    rw [Gamma0_mem] at hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have hNl_dvd_N : ((N / l : ℕ) : ℤ) ∣ (N : ℤ) := by
    refine ⟨(l : ℤ), ?_⟩
    have : (N / l) * l = N := Nat.div_mul_cancel h_dvd
    rw [show ((N : ℕ) : ℤ) = (((N / l) * l : ℕ) : ℤ) from by rw [this], Nat.cast_mul]
  have hNl_dvd_c : ((N / l : ℕ) : ℤ) ∣ γ.val 1 0 := dvd_trans hNl_dvd_N hN_dvd_c
  have h10_mod : ((γ.val 1 0 : ℤ) : ZMod (N / l)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNl_dvd_c
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · -- (0, 0) entry mod (N/l): from det γ = 1.
    show (((gtilde 0 0 : ℤ)) : ZMod (N / l)) = 1
    rw [show ((gtilde : SL(2, ℤ)) 0 0 : ℤ) = gtilde.val 0 0 from rfl, hgtilde_eq00]
    have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
      have hp := γ.property
      rwa [Matrix.det_fin_two] at hp
    have hdet_mod : ((γ.val 0 0 : ℤ) : ZMod (N/l)) * ((γ.val 1 1 : ℤ) : ZMod (N/l)) -
        ((γ.val 0 1 : ℤ) : ZMod (N/l)) * ((γ.val 1 0 : ℤ) : ZMod (N/l)) = 1 := by
      have := congr_arg (fun x : ℤ => ((x : ℤ) : ZMod (N/l))) hdet
      push_cast at this
      simpa using this
    rw [hγ_ker, mul_one, h10_mod, mul_zero, sub_zero] at hdet_mod
    exact hdet_mod
  · -- (1, 1) entry: gtilde.val 1 1 = γ.val 1 1, so mod (N/l) = 1.
    show (((gtilde 1 1 : ℤ)) : ZMod (N / l)) = 1
    rw [show ((gtilde : SL(2, ℤ)) 1 1 : ℤ) = gtilde.val 1 1 from rfl, hgtilde_eq11]
    exact hγ_ker
  · -- (1, 0) entry: gtilde.val 1 0 = γ.val 1 0 / l, and N/l | γ.val 1 0 / l since N | γ.val 1 0.
    show (((gtilde 1 0 : ℤ)) : ZMod (N / l)) = 0
    rw [show ((gtilde : SL(2, ℤ)) 1 0 : ℤ) = gtilde.val 1 0 from rfl, hgtilde_eq10]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨m, hm⟩ := hN_dvd_c
    rw [hm]
    have hN_eq : (N : ℤ) = (l : ℤ) * (N / l : ℕ) := by
      have : (N / l) * l = N := Nat.div_mul_cancel h_dvd
      rw [show ((N : ℕ) : ℤ) = (((N / l) * l : ℕ) : ℤ) from by rw [this], Nat.cast_mul]
      ring
    rw [hN_eq]
    have hl_ne : (l : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
    rw [show ((l : ℤ) * ((N / l : ℕ) : ℤ)) * m = (l : ℤ) * (((N / l : ℕ) : ℤ) * m) from by ring,
      Int.mul_ediv_cancel_left _ hl_ne]
    exact ⟨m, rfl⟩

/-- **Case B slash relation theorem.** Under the Case B hypothesis
`¬ χ.FactorsThrough (N/l)`, there exists `δ ∈ Γ₁(N/l)` and `c : ℂ` with
`c ≠ 1` such that `f ∣[k] mapGL ℝ δ = c • f`. This is the structural
slash-incompatibility condition: `f` is forced to satisfy a non-trivial
scalar slash relation under a level-`Γ₁(N/l)` matrix, which is incompatible
with `f` being a (non-zero) modular form at level `Γ₁(N/l)`.

The downstream conclusion `f = 0` is closed by T072 via the constructive
two-multiplier route — see `conductorTheoremCaseB_vanishing` and
`exists_T_factor_with_char_separation`. -/
theorem case_B_slash_relation
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_not_fac : ¬ χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f) :
    ∃ (δ : SL(2, ℤ)) (_ : δ ∈ Gamma1 (N / l)) (c : ℂ),
      c ≠ 1 ∧ f ∣[k] (mapGL ℝ δ : GL (Fin 2) ℝ) = c • f := by
  have hNl_dvd_N : (N / l) ∣ N := ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩
  obtain ⟨u, hu_ker, hu_chi⟩ := exists_unit_of_not_factorsThrough hNl_dvd_N h_not_fac
  obtain ⟨gu, hgu_eq⟩ := Gamma0MapUnits_surjective u
  set γ_u : SL(2, ℤ) := (gu : SL(2, ℤ))
  have hγu_mem : γ_u ∈ Gamma0 N := gu.property
  -- γ_u.val 1 1 ≡ 1 mod (N/l) from u being in the kernel.
  have hγu_ker : ((γ_u.val 1 1 : ℤ) : ZMod (N / l)) = 1 := by
    -- From hgu_eq : Gamma0MapUnits gu = u, extract value.
    have h_val_eq : ((γ_u.val 1 1 : ℤ) : ZMod N) = (u : ZMod N) := by
      have h1 : Gamma0Map N gu = ((γ_u.val 1 1 : ℤ) : ZMod N) := rfl
      have h2 : (Gamma0MapUnits gu : ZMod N) = Gamma0Map N gu := Gamma0MapUnits_val gu
      rw [← h1, ← h2, hgu_eq]
    -- From hu_ker : ZMod.unitsMap hNl_dvd_N u = 1, extract that u.val reduces to 1.
    have h_u_red : (ZMod.cast (u : ZMod N) : ZMod (N / l)) = 1 := by
      have := congr_arg Units.val hu_ker
      simpa [ZMod.unitsMap_val] using this
    -- Combine: ((γ_u.val 1 1 : ℤ) : ZMod (N/l)) =
    --         ZMod.cast (((γ_u.val 1 1 : ℤ) : ZMod N) : ZMod (N/l))
    --         = ZMod.cast (u : ZMod N) = 1.
    rw [← ZMod.cast_intCast hNl_dvd_N (γ_u.val 1 1) (R := ZMod (N / l)),
      h_val_eq, h_u_red]
  -- The lifted matrix.
  set delta := levelRaiseConjOfDvd l γ_u
    (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγu_mem)
  refine ⟨delta,
    levelRaiseConjOfDvd_mem_Gamma1_div_of_mem_ker l N h_dvd hγu_mem hγu_ker,
    (χ.toUnitHom (Gamma0MapUnits ⟨γ_u, hγu_mem⟩) : ℂ), ?_, ?_⟩
  · -- The character value is non-trivial.
    intro h_eq
    -- h_eq : (χ.toUnitHom (Gamma0MapUnits ⟨γ_u, hγu_mem⟩) : ℂ) = 1
    have hgu_eq' : Gamma0MapUnits ⟨γ_u, hγu_mem⟩ = u := hgu_eq
    rw [hgu_eq'] at h_eq
    -- h_eq : (χ.toUnitHom u : ℂ) = 1
    apply hu_chi
    exact Units.ext h_eq
  · -- The slash equation from conductor_slash_eq.
    exact conductor_slash_eq l N h_dvd k χ f g hg_char hg_eq γ_u hγu_mem

/-- **Algebraic two-multiplier contradiction.** If `f ∣[k] M` is BOTH `c₁ • f`
AND `c₂ • f` for two distinct scalars, then `f = 0`. This captures the
algebraic core of the Case B vanishing argument: when two factorizations of
the same matrix produce different `χ` multipliers, the underlying function
must vanish. -/
lemma fun_eq_zero_of_two_multipliers (k : ℤ) (f : UpperHalfPlane → ℂ)
    (M : GL (Fin 2) ℝ) {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (h₁ : f ∣[k] M = c₁ • f) (h₂ : f ∣[k] M = c₂ • f) :
    f = 0 := by
  have h_smul : c₁ • f = c₂ • f := h₁.symm.trans h₂
  have h_diff : (c₁ - c₂) • f = 0 := by
    rw [sub_smul, h_smul, sub_self]
  have hne' : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  rcases smul_eq_zero.mp h_diff with hc | hf
  · exact absurd hc hne'
  · exact hf

/-- **Case B vanishing — conditional form.** Under the Case B hypothesis
`¬ χ.FactorsThrough (N/l)`, the function `f` vanishes provided we have a
hypothesis `h_second_mult` producing a SECOND scalar `c' ≠ c` such that
`f ∣[k] mapGL ℝ δ = c' • f` for the witness matrix `δ`.

This is the algebraic interface used by the unconditional Case B
vanishing `conductorTheoremCaseB_vanishing` (T072): the latter discharges
`h_second_mult` by combining `case_B_slash_relation_with_controlled_lift`
with `exists_T_factor_with_char_separation` and then invoking
`conductor_slash_T_conj_eq` on the alternate `Γ₀(N)`-lift. -/
theorem case_B_vanishing_of_two_multipliers
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_not_fac : ¬ χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (h_second_mult : ∀ (δ : SL(2, ℤ)) (_ : δ ∈ Gamma1 (N / l)) (c : ℂ),
      c ≠ 1 → f ∣[k] (mapGL ℝ δ : GL (Fin 2) ℝ) = c • f →
      ∃ c' : ℂ, c' ≠ c ∧ f ∣[k] (mapGL ℝ δ : GL (Fin 2) ℝ) = c' • f) :
    f = 0 := by
  obtain ⟨δ, hδ_mem, c, hc_ne, hc_eq⟩ :=
    case_B_slash_relation l N h_dvd k χ h_not_fac f g hg_char hg_eq
  obtain ⟨c', hc'_ne, hc'_eq⟩ := h_second_mult δ hδ_mem c hc_ne hc_eq
  exact fun_eq_zero_of_two_multipliers k f
    ((mapGL ℝ δ : GL (Fin 2) ℝ)) hc'_ne.symm hc_eq hc'_eq

/-! ### Controlled `Γ₀(N)` lift with prescribed `(1, 0)` entry (T071)

For the constructive Case B vanishing route (alternate `(i, j)` factorization
via T046), we need a `Γ₀(N)` lift `γ` of a unit `u : (ZMod N)ˣ` with the
ADDITIONAL property that `γ.val 1 0 = N` (the SMALLEST positive lift of `0`,
not just any multiple of `N`). This makes downstream divisibility analysis
tractable, since the conjugate `γ̃ = α_l γ α_l⁻¹` has `γ̃.val 1 0 = N/l`
and the (i, j)-shift constraint becomes a linear congruence mod `l`. -/

/-- **Controlled `Γ₀(N)` lift.** Explicit Bezout-style matrix
`!![a, b; N, e]` with `a = (u⁻¹ : ZMod N).val`, `e = (u : ZMod N).val`
(canonical integer representatives in `[0, N)`), and `b = (a*e - 1) / N`
(integer because `a*e ≡ 1 mod N`). This lies in `SL(2, ℤ)` (det = 1) and
in `Γ₀(N)` (lower-left entry `N ≡ 0 mod N`); its `Gamma0MapUnits` value is
exactly `u`. -/
noncomputable def gamma0LiftLowerLeftN (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ↥(Gamma0 N) := by
  let e : ℤ := ((u.val : ZMod N).val : ℤ)
  let a : ℤ := ((u⁻¹.val : ZMod N).val : ℤ)
  -- a * e ≡ 1 mod N from u * u⁻¹ = 1.
  have h_ae : ((a * e : ℤ) : ZMod N) = 1 := by
    show (((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ)) : ℤ) : ZMod N) = 1
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h_dvd : (N : ℤ) ∣ (a * e - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [show ((a : ZMod N) * (e : ZMod N) - 1 : ZMod N) =
        ((a * e : ℤ) : ZMod N) - 1 from by push_cast; ring]
    rw [h_ae]; ring
  let b : ℤ := (a * e - 1) / (N : ℤ)
  refine ⟨⟨!![a, b; (N : ℤ), e], ?det⟩, ?gamma0⟩
  · -- det = a*e - b*N = 1
    rw [Matrix.det_fin_two_of]
    show a * e - b * (N : ℤ) = 1
    have : b * (N : ℤ) = a * e - 1 :=
      Int.ediv_mul_cancel h_dvd
    linarith
  · -- (1, 0) entry = N, mod N = 0
    rw [Gamma0_mem]
    show (((N : ℤ) : ℤ) : ZMod N) = 0
    simp

/-- The `(1, 0)` entry of `gamma0LiftLowerLeftN N u` equals `N`. -/
@[simp]
lemma gamma0LiftLowerLeftN_lower_left (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 0 : ℤ) = (N : ℤ) := rfl

/-- The `(1, 1)` entry of `gamma0LiftLowerLeftN N u` is `(u : ZMod N).val`. -/
@[simp]
lemma gamma0LiftLowerLeftN_lower_right (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 1 : ℤ) =
      ((u.val : ZMod N).val : ℤ) := rfl

/-- The `(0, 0)` entry of `gamma0LiftLowerLeftN N u` is `(u⁻¹ : ZMod N).val`. -/
@[simp]
lemma gamma0LiftLowerLeftN_upper_left (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 0 : ℤ) =
      ((u⁻¹.val : ZMod N).val : ℤ) := rfl

/-- `Gamma0MapUnits` of the controlled lift recovers the original unit. -/
@[simp]
lemma gamma0LiftLowerLeftN_Gamma0MapUnits (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    Gamma0MapUnits (gamma0LiftLowerLeftN N u) = u := by
  apply Units.ext
  show Gamma0Map N (gamma0LiftLowerLeftN N u) = (u : ZMod N)
  show ((((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 1 : ℤ)) : ZMod N) = (u : ZMod N)
  rw [gamma0LiftLowerLeftN_lower_right]
  push_cast
  rw [ZMod.natCast_zmod_val]

/-- **Refined Case B slash relation** using the controlled lift
`gamma0LiftLowerLeftN`. Same conclusion as `case_B_slash_relation` but
uses an explicit `Γ₀(N)` lift `γ_u` with `γ_u.val 1 0 = N`, exposing this
property for downstream constructive analysis (e.g., the `(i, j)`-shift
divisibility solver in T071). -/
lemma case_B_slash_relation_with_controlled_lift
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_not_fac : ¬ χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f) :
    ∃ (u : (ZMod N)ˣ),
      ZMod.unitsMap ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ u = 1 ∧
      χ.toUnitHom u ≠ 1 ∧
      ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 0 : ℤ) = (N : ℤ) ∧
      f ∣[k]
        (mapGL ℝ
          (levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u : SL(2, ℤ))
            (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
              (gamma0LiftLowerLeftN N u).property))
        : GL (Fin 2) ℝ) =
        (χ.toUnitHom u : ℂ) • f := by
  have hNl_dvd_N : (N / l) ∣ N := ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩
  obtain ⟨u, hu_ker, hu_chi⟩ := exists_unit_of_not_factorsThrough hNl_dvd_N h_not_fac
  refine ⟨u, hu_ker, hu_chi, gamma0LiftLowerLeftN_lower_left N u, ?_⟩
  -- Apply conductor_slash_eq to gamma0LiftLowerLeftN N u.
  have h_slash := conductor_slash_eq l N h_dvd k χ f g hg_char hg_eq
    (gamma0LiftLowerLeftN N u : SL(2, ℤ)) (gamma0LiftLowerLeftN N u).property
  -- Convert χ value: Gamma0MapUnits (...) = u.
  rw [show Gamma0MapUnits ⟨(gamma0LiftLowerLeftN N u : SL(2, ℤ)),
      (gamma0LiftLowerLeftN N u).property⟩ = u from
    gamma0LiftLowerLeftN_Gamma0MapUnits N u] at h_slash
  exact h_slash

/-! ### Divisibility analysis for `(i, j)`-shifts (T071)

Given the controlled lift `γ_u = gamma0LiftLowerLeftN N u` (with
`γ_u.val 1 0 = N`), the conjugate `γ̃_u := α_l γ_u α_l⁻¹` has
`γ̃_u.val 1 0 = N/l`. For the alternate factorization
`δ = T^i (α_l γ' α_l⁻¹) T^j` to give a valid `Γ₀(N)`-lift `γ'`, the
`(0, 1)` entry of `T^{-i} γ̃_u T^{-j}` must be divisible by `l`.

This entry equals `-j*(γ_u.val 0 0 - i*(N/l)) + l*(γ_u.val 0 1) - i*(γ_u.val 1 1)`.
Modulo `l`, the divisibility reduces to:

```
  i * γ_u.val 1 1 + j * γ_u.val 0 0 - i * j * (N/l) ≡ 0 mod l
```

This `(i, j)` constraint is what determines which alternate lifts are
admissible. The corresponding alternate-lift `γ'` then has
`γ'.val 1 1 = γ_u.val 1 1 - j * (N/l)`, i.e., shifts in the kernel. -/

/-- **Algebraic obstruction summary**: the `(0, 1)` entry of the shifted
matrix `T^{-i} γ̃_u T^{-j}` (where `γ̃_u = α_l γ_u α_l⁻¹` with
`γ_u.val 1 0 = N`) equals
`-j*(γ_u.val 0 0 - i*(N/l)) + l*γ_u.val 0 1 - i*γ_u.val 1 1`.
Divisibility by `l` reduces (since `l | l*γ_u.val 0 1`) to the
congruence
`l ∣ i*γ_u.val 1 1 + j*γ_u.val 0 0 - i*j*(N/l)`. This is the precise
condition that `(i, j)` must satisfy for the alternate factorization
to yield a `Γ₀(N)`-lift.

(Stated as a separate identity for downstream use; the divisibility
analysis itself remains an open construction in T071.) -/
lemma T_shift_divisibility_eq_iff
    (l N : ℕ) (i j : ℤ) (a₀ b₀ e₀ : ℤ) :
    (l : ℤ) ∣ (-j * (a₀ - i * ((N / l : ℕ) : ℤ)) + l * b₀ - i * e₀) ↔
      (l : ℤ) ∣ (i * e₀ + j * a₀ - i * j * ((N / l : ℕ) : ℤ)) := by
  constructor
  · intro h
    have h1 : (l : ℤ) ∣ -(- j * (a₀ - i * ((N / l : ℕ) : ℤ)) + l * b₀ - i * e₀) := by
      exact (dvd_neg).mpr h
    have h2 : (-(- j * (a₀ - i * ((N / l : ℕ) : ℤ)) + l * b₀ - i * e₀)) =
        (i * e₀ + j * a₀ - i * j * ((N / l : ℕ) : ℤ)) - l * b₀ := by ring
    rw [h2] at h1
    have hl_lb₀ : (l : ℤ) ∣ l * b₀ := ⟨b₀, rfl⟩
    have : (l : ℤ) ∣ ((i * e₀ + j * a₀ - i * j * ((N / l : ℕ) : ℤ)) - l * b₀ + l * b₀) :=
      dvd_add h1 hl_lb₀
    simpa using this
  · intro h
    have h1 : (l : ℤ) ∣ (i * e₀ + j * a₀ - i * j * ((N / l : ℕ) : ℤ)) := h
    have hl_lb₀ : (l : ℤ) ∣ l * b₀ := ⟨b₀, rfl⟩
    have : (l : ℤ) ∣ -((i * e₀ + j * a₀ - i * j * ((N / l : ℕ) : ℤ)) - l * b₀) := by
      apply dvd_neg.mpr
      exact dvd_sub h1 hl_lb₀
    have h2 : -((i * e₀ + j * a₀ - i * j * ((N / l : ℕ) : ℤ)) - l * b₀) =
        (- j * (a₀ - i * ((N / l : ℕ) : ℤ)) + l * b₀ - i * e₀) := by ring
    rw [h2] at this
    exact this

/-! ### Character separation in the kernel (T071 continuation)

The Case B closure requires finding a unit `v ∈ ker((ZMod N)ˣ → (ZMod (N/l))ˣ)`
such that `χ.toUnitHom (u * v) ≠ χ.toUnitHom u` (multiplicative form).
This is provable directly from `¬ χ.FactorsThrough (N/l)` via
`exists_unit_of_not_factorsThrough`. -/

/-- **Multiplicative character separation in the kernel.** Given any
`u : (ZMod N)ˣ` and `χ` not factoring through level `d`, there is a
kernel element `v` (with `ZMod.unitsMap hd v = 1`) such that
`χ.toUnitHom (u * v) ≠ χ.toUnitHom u`. The witness is any
`v ∈ ker(ZMod.unitsMap hd) ∖ ker(χ.toUnitHom)`, which exists by
`exists_unit_of_not_factorsThrough`. -/
lemma exists_kernel_unit_with_char_shift
    {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    {χ : DirichletCharacter ℂ N} (h_not_fac : ¬ χ.FactorsThrough d)
    (u : (ZMod N)ˣ) :
    ∃ v : (ZMod N)ˣ, ZMod.unitsMap hd v = 1 ∧
      χ.toUnitHom (u * v) ≠ χ.toUnitHom u := by
  obtain ⟨v, hv_ker, hv_chi⟩ := exists_unit_of_not_factorsThrough hd h_not_fac
  refine ⟨v, hv_ker, ?_⟩
  intro h
  apply hv_chi
  -- From χ(u*v) = χ(u): χ(u)*χ(v) = χ(u), so χ(v) = 1.
  have h1 : χ.toUnitHom u * χ.toUnitHom v = χ.toUnitHom u * 1 := by
    rw [← map_mul, h, mul_one]
  exact mul_left_cancel h1

/-- **Integer-`j`-shift bridge** (T071 ZMod arithmetic). For `v : (ZMod N)ˣ`
in `ker((ZMod N)ˣ → (ZMod (N/l))ˣ)`, the integer representative `v.val`
of the underlying `ZMod N` element satisfies `(N/l) ∣ (v.val - 1)` (in `ℤ`).
This converts the multiplicative kernel data into an integer
divisibility, the form needed by the `T_shift_divisibility_eq_iff`
analysis. -/
lemma natCast_val_sub_one_dvd_of_mem_ker
    {N l : ℕ} [NeZero N] [NeZero l] (h_dvd : l ∣ N)
    (v : (ZMod N)ˣ)
    (hv_ker : ZMod.unitsMap ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ v = 1) :
    ((N / l : ℕ) : ℤ) ∣ (((v : ZMod N).val : ℤ) - 1) := by
  have hNl_dvd_N : (N / l) ∣ N := ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩
  -- From hv_ker: castHom hNl_dvd_N (v.val) = 1 in ZMod (N/l).
  have h_cast_one : ZMod.castHom hNl_dvd_N (ZMod (N / l)) (v : ZMod N) = 1 := by
    have hh := congr_arg Units.val hv_ker
    rw [ZMod.unitsMap_val, Units.val_one] at hh
    exact hh
  -- Goal: (N/l) | (v.val - 1) in ℤ.
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  -- Goal: ((((v : ZMod N).val : ℤ) - 1 : ℤ) : ZMod (N / l)) = 0
  push_cast
  -- Goal: (((v : ZMod N).val : ℕ) : ZMod (N/l)) - 1 = 0  (after push_cast)
  rw [ZMod.natCast_val (v : ZMod N)]
  -- Goal: ZMod.cast (v : ZMod N) - 1 = 0  (in ZMod (N/l))
  rw [show (ZMod.cast ((v : ZMod N) : ZMod N) : ZMod (N / l)) =
      ZMod.castHom hNl_dvd_N (ZMod (N / l)) (v : ZMod N) from rfl,
    h_cast_one]
  ring

/-- **Coset character separation** (T071 main existence theorem).
Under the Case B hypothesis `¬ χ.FactorsThrough d`, for any `u : (ZMod N)ˣ`,
there exists `u' : (ZMod N)ˣ` in the same `ZMod.unitsMap hd`-coset as `u`
(equivalently, `u' = u * v` for some kernel unit `v`) with
`χ.toUnitHom u' ≠ χ.toUnitHom u`. This is the precise multiplicative
form of the χ-separation needed by Case B vanishing. -/
lemma exists_alt_unit_in_coset_with_char_separation
    {N : ℕ} [NeZero N] {d : ℕ} (hd : d ∣ N)
    {χ : DirichletCharacter ℂ N} (h_not_fac : ¬ χ.FactorsThrough d)
    (u : (ZMod N)ˣ) :
    ∃ u' : (ZMod N)ˣ,
      ZMod.unitsMap hd u' = ZMod.unitsMap hd u ∧
      χ.toUnitHom u' ≠ χ.toUnitHom u := by
  obtain ⟨v, hv_ker, hv_chi⟩ := exists_kernel_unit_with_char_shift hd h_not_fac u
  refine ⟨u * v, ?_, ?_⟩
  · -- ZMod.unitsMap hd (u * v) = ZMod.unitsMap hd u
    rw [map_mul, hv_ker, mul_one]
  · -- χ(u * v) ≠ χ(u)
    exact hv_chi

/-- **Generalized integer-shift bridge** (T072): if two units `u, u'` lie in
the same `ZMod.unitsMap hd`-coset, then `(N/l) ∣ (u.val.val - u'.val.val)` in
`ℤ`. Companion to `natCast_val_sub_one_dvd_of_mem_ker`; this is the
two-unit form needed to construct the integer shift `j = (e₀ - e₀')/(N/l)`
in the matrix identity for `exists_T_factor_with_char_separation`. -/
lemma natCast_val_sub_dvd_of_unitsMap_eq
    {N l : ℕ} [NeZero N] [NeZero l] (h_dvd : l ∣ N)
    (u u' : (ZMod N)ˣ)
    (h_eq : ZMod.unitsMap ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ u =
            ZMod.unitsMap ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ u') :
    ((N / l : ℕ) : ℤ) ∣ (((u : ZMod N).val : ℤ) - ((u' : ZMod N).val : ℤ)) := by
  have hNl_dvd_N : (N / l) ∣ N := ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩
  have h_cast_eq : ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u : ZMod N) =
      ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u' : ZMod N) := by
    have hh := congr_arg Units.val h_eq
    rw [ZMod.unitsMap_val, ZMod.unitsMap_val] at hh
    exact hh
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val (u : ZMod N), ZMod.natCast_val (u' : ZMod N)]
  rw [show (ZMod.cast ((u : ZMod N) : ZMod N) : ZMod (N / l)) =
        ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u : ZMod N) from rfl,
    show (ZMod.cast ((u' : ZMod N) : ZMod N) : ZMod (N / l)) =
        ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u' : ZMod N) from rfl,
    h_cast_eq]
  ring

/-! ### T-factor matrix construction with character separation (T072)

The main theorem of this section builds the alternate `Γ₀(N)`-lift `γ'`
explicitly using the controlled lift `gamma0LiftLowerLeftN`, plus the
explicit integer shifts `i, j` derived from the divisibility lemma above.
Crucially, the matrix identity `γ̃_u = T^i · γ̃' · T^j` holds with
`i = (a₀ - a₀') / (N/l)` and `j = (e₀ - e₀') / (N/l)` — both integer by
the kernel-coset divisibility, with cancellation verified by the
determinant identity `a₀*e₀ - b₀*N = a₀'*e₀' - b₀'*N = 1`. -/

/-- The `(0, 1)` entry of the controlled lift `gamma0LiftLowerLeftN N u` is
the Bezout coefficient `b = (a*e - 1) / N` (where `a = u⁻¹.val.val`,
`e = u.val.val`). Proved by direct unfolding. -/
@[simp]
lemma gamma0LiftLowerLeftN_upper_right (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 1 : ℤ) =
      (((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) /
        (N : ℤ) := rfl

/-- **Matrix identity helper** (T072). For pure 2×2 integer matrices: given
the shift conditions `i*Nl = a - a'` and `j*Nl = e - e'`, plus the
determinant identities `a*e - b*(l*Nl) = 1` and `a'*e' - b'*(l*Nl) = 1`,
the matrix identity
`!![a, l*b; Nl, e] = !![1, i; 0, 1] * !![a', l*b'; Nl, e'] * !![1, j; 0, 1]`
holds, provided `Nl ≠ 0`. -/
private lemma t_factor_matrix_identity
    {l Nl i j a a' e e' b b' : ℤ} (hNl : Nl ≠ 0)
    (h_i : i * Nl = a - a') (h_j : j * Nl = e - e')
    (h_det : a * e - b * (l * Nl) = 1)
    (h_det' : a' * e' - b' * (l * Nl) = 1) :
    (!![a, l * b; Nl, e] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(1 : ℤ), i; 0, 1] * !![a', l * b'; Nl, e'] *
        !![(1 : ℤ), j; 0, 1] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · -- (0, 0): a = a' + i*Nl
    linarith
  · -- (0, 1): l*b = (a' + i*Nl)*j + l*b' + i*e'
    -- Multiply by Nl and use the determinant identities.
    apply mul_left_cancel₀ hNl
    linear_combination -h_det + h_det' + (-e' - Nl * j) * h_i + (-a) * h_j
  · -- (1, 1): e = j*Nl + e'.
    linarith

/-- The determinant divisibility for the controlled lift: `N` divides
`u⁻¹.val.val * u.val.val - 1` in `ℤ`, since `u⁻¹ * u = 1` in `(ZMod N)ˣ`. -/
private lemma N_dvd_inv_val_mul_val_sub_one (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (N : ℤ) ∣ (((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have h_unit : u⁻¹.val * u.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h_unit]
  ring

/-- **Determinant identity for the controlled lift**:
`a₀ * e₀ - b₀ * N = 1` where `b₀ = (a₀ * e₀ - 1) / N`. -/
private lemma controlled_lift_det_identity (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) -
      ((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) / (N : ℤ)) *
        (N : ℤ) = 1 := by
  have h := N_dvd_inv_val_mul_val_sub_one N u
  have h_eq : ((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) /
      (N : ℤ)) * (N : ℤ) =
      ((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1 :=
    Int.ediv_mul_cancel h
  linarith

/-- **Explicit T-factor with character separation** (T072 main theorem).
Given the Case B hypothesis (`¬ FactorsThrough`) and a unit `u`, construct
an integer pair `(i, j)` and a separating unit `u'` (in the same
`unitsMap`-coset as `u`) such that:
  (a) `χ.toUnitHom u' ≠ χ.toUnitHom u`, AND
  (b) the matrix identity
      `levelRaiseConjOfDvd l γ_u = T^i · levelRaiseConjOfDvd l γ' · T^j`
      holds for `γ_u = gamma0LiftLowerLeftN N u` and
      `γ' = gamma0LiftLowerLeftN N u'`.

Combined with `conductor_slash_T_conj_eq` (T044), this yields the SECOND
slash multiplier needed by `case_B_vanishing_of_two_multipliers` to
deduce `f = 0`. -/
theorem exists_T_factor_with_char_separation
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N)
    (χ : DirichletCharacter ℂ N) (h_not_fac : ¬ χ.FactorsThrough (N / l))
    (u : (ZMod N)ˣ) :
    ∃ (i j : ℤ) (u' : (ZMod N)ˣ),
      χ.toUnitHom u' ≠ χ.toUnitHom u ∧
      levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u : SL(2, ℤ))
        (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
          (gamma0LiftLowerLeftN N u).property) =
      (ModularGroup.T : SL(2, ℤ)) ^ i *
        levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u' : SL(2, ℤ))
          (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
            (gamma0LiftLowerLeftN N u').property) *
        (ModularGroup.T : SL(2, ℤ)) ^ j := by
  have hNl_dvd_N : (N / l) ∣ N := ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩
  obtain ⟨u', hu'_coset, hu'_chi⟩ :=
    exists_alt_unit_in_coset_with_char_separation hNl_dvd_N h_not_fac u
  -- Entries.
  set a₀ : ℤ := ((u⁻¹.val : ZMod N).val : ℤ)
  set e₀ : ℤ := ((u.val : ZMod N).val : ℤ)
  set a₀' : ℤ := ((u'⁻¹.val : ZMod N).val : ℤ)
  set e₀' : ℤ := ((u'.val : ZMod N).val : ℤ)
  set b₀ : ℤ := (a₀ * e₀ - 1) / (N : ℤ)
  set b₀' : ℤ := (a₀' * e₀' - 1) / (N : ℤ)
  set Nl : ℤ := ((N / l : ℕ) : ℤ)
  -- Divisibility lemmas.
  have h_dvd_e : Nl ∣ (e₀ - e₀') :=
    natCast_val_sub_dvd_of_unitsMap_eq h_dvd u u' hu'_coset.symm
  have h_dvd_a : Nl ∣ (a₀ - a₀') := by
    apply natCast_val_sub_dvd_of_unitsMap_eq h_dvd u⁻¹ u'⁻¹
    rw [map_inv, map_inv, hu'_coset]
  set i : ℤ := (a₀ - a₀') / Nl
  set j : ℤ := (e₀ - e₀') / Nl
  refine ⟨i, j, u', hu'_chi, ?_⟩
  have h_i_eq : i * Nl = a₀ - a₀' := Int.ediv_mul_cancel h_dvd_a
  have h_j_eq : j * Nl = e₀ - e₀' := Int.ediv_mul_cancel h_dvd_e
  have hN_eq : (N : ℤ) = (l : ℤ) * Nl := by
    have h_nat : (N / l) * l = N := Nat.div_mul_cancel h_dvd
    show ((N : ℕ) : ℤ) = (l : ℤ) * ((N / l : ℕ) : ℤ)
    rw [show ((N : ℕ) : ℤ) = (((N / l) * l : ℕ) : ℤ) from by rw [h_nat], Nat.cast_mul]
    ring
  have hNl_ne : Nl ≠ 0 := by
    have h_pos : 0 < N / l := by
      have hl_pos : 0 < l := Nat.pos_of_neZero l
      have hN_pos : 0 < N := Nat.pos_of_neZero N
      exact Nat.div_pos (Nat.le_of_dvd hN_pos h_dvd) hl_pos
    show ((N / l : ℕ) : ℤ) ≠ 0
    exact_mod_cast h_pos.ne'
  have h_det_u : a₀ * e₀ - b₀ * ((l : ℤ) * Nl) = 1 := by
    rw [← hN_eq]; exact controlled_lift_det_identity N u
  have h_det_u' : a₀' * e₀' - b₀' * ((l : ℤ) * Nl) = 1 := by
    rw [← hN_eq]; exact controlled_lift_det_identity N u'
  -- Matrix identity via t_factor_matrix_identity.
  have h_mat_id :
      (!![a₀, (l : ℤ) * b₀; Nl, e₀] : Matrix (Fin 2) (Fin 2) ℤ) =
        !![(1 : ℤ), i; 0, 1] * !![a₀', (l : ℤ) * b₀'; Nl, e₀'] *
          !![(1 : ℤ), j; 0, 1] :=
    t_factor_matrix_identity hNl_ne h_i_eq h_j_eq h_det_u h_det_u'
  -- Convert to SL(2, ℤ) equality.
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow]
  -- Show LHS.val and RHS.val match the matrix forms.
  have h_lhs_val : (levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u : SL(2, ℤ))
      (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
        (gamma0LiftLowerLeftN N u).property)).val =
      (!![a₀, (l : ℤ) * b₀; Nl, e₀] : Matrix (Fin 2) (Fin 2) ℤ) := by
    show (Matrix.of !![(gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 0,
        (l : ℤ) * (gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 1;
        (gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 0 / l,
        (gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 1] : Matrix _ _ ℤ) =
      !![a₀, (l : ℤ) * b₀; Nl, e₀]
    have hl_ne : (l : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
    have h_div_eq : (N : ℤ) / (l : ℤ) = Nl := by
      rw [hN_eq, Int.mul_ediv_cancel_left _ hl_ne]
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [gamma0LiftLowerLeftN_upper_left, gamma0LiftLowerLeftN_upper_right,
        gamma0LiftLowerLeftN_lower_left, gamma0LiftLowerLeftN_lower_right,
        h_div_eq, e₀, a₀, b₀]
  have h_rhs_val : (levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u' : SL(2, ℤ))
      (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
        (gamma0LiftLowerLeftN N u').property)).val =
      (!![a₀', (l : ℤ) * b₀'; Nl, e₀'] : Matrix (Fin 2) (Fin 2) ℤ) := by
    show (Matrix.of !![(gamma0LiftLowerLeftN N u' : SL(2, ℤ)).val 0 0,
        (l : ℤ) * (gamma0LiftLowerLeftN N u' : SL(2, ℤ)).val 0 1;
        (gamma0LiftLowerLeftN N u' : SL(2, ℤ)).val 1 0 / l,
        (gamma0LiftLowerLeftN N u' : SL(2, ℤ)).val 1 1] : Matrix _ _ ℤ) =
      !![a₀', (l : ℤ) * b₀'; Nl, e₀']
    have hl_ne : (l : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
    have h_div_eq : (N : ℤ) / (l : ℤ) = Nl := by
      rw [hN_eq, Int.mul_ediv_cancel_left _ hl_ne]
    ext p q; fin_cases p <;> fin_cases q <;>
      simp [gamma0LiftLowerLeftN_upper_left, gamma0LiftLowerLeftN_upper_right,
        gamma0LiftLowerLeftN_lower_left, gamma0LiftLowerLeftN_lower_right,
        h_div_eq, e₀', a₀', b₀']
  rw [h_lhs_val, h_rhs_val]
  exact h_mat_id

/-- **Case B vanishing theorem (T072 closure)**: under the Case B hypothesis
`¬ χ.FactorsThrough (N/l)` plus the period-1 hypothesis on `f`, the
candidate lower-level form `f` vanishes. The proof composes the slash
relation from `case_B_slash_relation_with_controlled_lift` with the
alternative slash multiplier produced by `exists_T_factor_with_char_separation`
+ `conductor_slash_T_conj_eq` (T044), then closes via the algebraic
two-multiplier contradiction `fun_eq_zero_of_two_multipliers`. -/
theorem conductorTheoremCaseB_vanishing
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_not_fac : ¬ χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    f = 0 := by
  -- Step 1: Get the original slash relation via the controlled lift.
  obtain ⟨u, _, _, _, h_slash⟩ :=
    case_B_slash_relation_with_controlled_lift l N h_dvd k χ h_not_fac f g
      hg_char hg_eq
  -- Step 2: Get the T-factor and separating unit.
  obtain ⟨i, j, u', hu'_chi, h_mat_id⟩ :=
    exists_T_factor_with_char_separation l N h_dvd χ h_not_fac u
  -- Step 3: Apply conductor_slash_T_conj_eq with γ_u' = gamma0LiftLowerLeftN N u'.
  have h_slash_alt :=
    conductor_slash_T_conj_eq l N h_dvd k χ f g hg_char hg_eq hf_period
      i j (gamma0LiftLowerLeftN N u' : SL(2, ℤ))
      (gamma0LiftLowerLeftN N u').property
  -- h_slash_alt : f ∣[k] mapGL ℝ (T^i * γ̃_{u'} * T^j) =
  --   (χ.toUnitHom (Gamma0MapUnits ⟨γ_{u'}, _⟩) : ℂ) • f
  -- Rewrite Gamma0MapUnits γ_{u'} = u'.
  have h_gamma : Gamma0MapUnits
      ⟨(gamma0LiftLowerLeftN N u' : SL(2, ℤ)),
        (gamma0LiftLowerLeftN N u').property⟩ = u' :=
    gamma0LiftLowerLeftN_Gamma0MapUnits N u'
  rw [h_gamma] at h_slash_alt
  -- Use h_mat_id to substitute T^i * γ̃_{u'} * T^j back to γ̃_u.
  rw [← h_mat_id] at h_slash_alt
  -- Now h_slash and h_slash_alt have the same LHS but multipliers χ(u) vs χ(u').
  -- Apply fun_eq_zero_of_two_multipliers.
  have hne : (χ.toUnitHom u : ℂ) ≠ (χ.toUnitHom u' : ℂ) :=
    fun h => hu'_chi.symm (Units.ext h)
  exact fun_eq_zero_of_two_multipliers k f _ hne h_slash h_slash_alt

/-! ### Conductor theorem dichotomy (T075)

Combining T064 (Case A bundling) and T072 (Case B vanishing) yields the
full Miyake §4.6.4 dichotomy. -/

/-- **Miyake 4.6.4 Conductor theorem (modular form flavor)**: under the
generic Case A/B hypotheses, EITHER `χ` factors through level `N/l` and
`f` bundles into a `ModularForm` at the lowered level, OR `f = 0`. -/
theorem conductor_theorem_dichotomy
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    (∃ _ : χ.FactorsThrough (N / l),
      ∃ F : ModularForm ((Gamma1 (N / l)).map (mapGL ℝ)) k, ⇑F = f) ∨
    f = 0 := by
  classical
  by_cases h_fac : χ.FactorsThrough (N / l)
  · left
    refine ⟨h_fac, conductorTheoremCaseA_modularForm l N h_dvd k χ h_fac f g
      hg_char hg_eq hf_period, ?_⟩
    exact conductorTheoremCaseA_modularForm_apply l N h_dvd k χ h_fac f g
      hg_char hg_eq hf_period
  · right
    exact conductorTheoremCaseB_vanishing l N h_dvd k χ h_fac f g hg_char hg_eq
      hf_period

/-- **Miyake 4.6.4 Conductor theorem (cusp form flavor)**: under the
generic Case A/B hypotheses with `g : CuspForm`, EITHER `χ` factors
through level `N/l` and `f` bundles into a `CuspForm` at the lowered
level, OR `f = 0`. The Case B branch reduces to the modular-form
`conductorTheoremCaseB_vanishing` via `cuspFormToModularForm`. -/
theorem conductor_theorem_dichotomy_cuspForm
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    (∃ _ : χ.FactorsThrough (N / l),
      ∃ F : CuspForm ((Gamma1 (N / l)).map (mapGL ℝ)) k, ⇑F = f) ∨
    f = 0 := by
  classical
  by_cases h_fac : χ.FactorsThrough (N / l)
  · left
    refine ⟨h_fac, conductorTheoremCaseA_cuspForm l N h_dvd k χ h_fac f g
      hg_char hg_eq hf_period, ?_⟩
    exact conductorTheoremCaseA_cuspForm_apply l N h_dvd k χ h_fac f g
      hg_char hg_eq hf_period
  · right
    -- Apply the modular-form Case B with g viewed as a ModularForm.
    have hg_mod_char : cuspFormToModularForm g ∈ modFormCharSpace k χ.toUnitHom :=
      (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        k χ.toUnitHom g).mpr hg_char
    exact conductorTheoremCaseB_vanishing l N h_dvd k χ h_fac f
      (cuspFormToModularForm g) hg_mod_char hg_eq hf_period

/-! ### Lowered character-space packaging (T077)

The Case A bundles produce ModularForm/CuspForm at level `Γ₁(N/l)`. To
feed Miyake's Main Lemma (POST-6e), we need to know these bundles also
lie in the LOWERED Nebentypus character space `modFormCharSpace k
(loweredCharacter h_fac).toUnitHom` (and the CuspForm analogue). -/

/-- **Helper**: for `γ ∈ Γ₀(N)` lifting `γ'_pkg ∈ ↥(Gamma0 (N/l))` via T046
with `γ.val 1 1 = γ'.val 1 1 - γ'.val 1 0 * j`, the units
`Gamma0MapUnits γ` (in `(ZMod N)ˣ`) and `Gamma0MapUnits γ'_pkg` (in
`(ZMod (N/l))ˣ`) agree under the reduction `ZMod.unitsMap`. -/
private lemma unitsMap_Gamma0MapUnits_lift_eq_of_diag
    (l N : ℕ) [NeZero N] [NeZero (N / l)] (h_dvd : l ∣ N)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N)
    (γ'_pkg : ↥(Gamma0 (N / l)))
    (j : ℤ)
    (hdiag : γ.val 1 1 =
      (γ'_pkg : SL(2, ℤ)).val 1 1 - (γ'_pkg : SL(2, ℤ)).val 1 0 * j) :
    ZMod.unitsMap (⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ : (N / l) ∣ N)
        (Gamma0MapUnits ⟨γ, hγ⟩) =
      Gamma0MapUnits γ'_pkg := by
  apply Units.ext
  have hNl_dvd_N : (N / l) ∣ N := ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩
  have hLHS_eq :
      (ZMod.unitsMap hNl_dvd_N (Gamma0MapUnits ⟨γ, hγ⟩)).val =
        (((γ.val 1 1 : ℤ)) : ZMod (N / l)) := by
    rw [ZMod.unitsMap_val]
    show ZMod.castHom hNl_dvd_N (ZMod (N / l)) (Gamma0Map N ⟨γ, hγ⟩) = _
    show ZMod.castHom hNl_dvd_N (ZMod (N / l))
      (((γ.val 1 1 : ℤ)) : ZMod N) = _
    exact ZMod.cast_intCast hNl_dvd_N (γ.val 1 1)
  rw [hLHS_eq]
  show (((γ.val 1 1 : ℤ)) : ZMod (N / l)) = Gamma0Map (N / l) γ'_pkg
  show (((γ.val 1 1 : ℤ)) : ZMod (N / l)) =
    (((γ'_pkg : SL(2, ℤ)).val 1 1 : ℤ) : ZMod (N / l))
  rw [hdiag]
  have h10_zero :
      (((γ'_pkg : SL(2, ℤ)).val 1 0 : ℤ) : ZMod (N / l)) = 0 := by
    have hγ' : (γ'_pkg : SL(2, ℤ)) ∈ Gamma0 (N / l) := γ'_pkg.property
    rw [Gamma0_mem] at hγ'
    exact hγ'
  push_cast
  rw [h10_zero]
  ring

/-- **Lowered character space membership for the modular-form Case A bundle**
(T077 main result, modular-form flavor). The bundle
`conductorTheoremCaseA_modularForm` lies in
`modFormCharSpace k (loweredCharacter h_fac).toUnitHom`. -/
theorem conductorTheoremCaseA_modularForm_mem_modFormCharSpace
    (l N : ℕ) [NeZero l] [NeZero N] [NeZero (N / l)] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_fac : χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ) (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    conductorTheoremCaseA_modularForm l N h_dvd k χ h_fac f g hg_char hg_eq
        hf_period ∈
      modFormCharSpace k (loweredCharacter h_fac).toUnitHom := by
  rw [modFormCharSpace_iff_nebentypus]
  intro γ'_pkg
  rw [conductorTheoremCaseA_modularForm_apply]
  -- Goal: f ∣[k] mapGL ℝ γ'.val =
  --       ((loweredCharacter h_fac).toUnitHom (Gamma0MapUnits γ'_pkg) : ℂ) • f
  -- Use exists_T_levelRaiseConj_T_factor to factorize γ'_pkg.
  obtain ⟨i, j, γ, hγ, hfact, hdiag⟩ :=
    exists_T_levelRaiseConj_T_factor l N h_dvd γ'_pkg.val γ'_pkg.property
  rw [hfact]
  -- Apply conductor_slash_T_conj_eq.
  rw [conductor_slash_T_conj_eq l N h_dvd k χ f g hg_char hg_eq hf_period i j γ hγ]
  -- Rewrite χ.toUnitHom via toUnitHom_loweredCharacter and unitsMap relation.
  congr 2
  rw [toUnitHom_loweredCharacter h_fac, MonoidHom.comp_apply]
  congr 1
  -- Goal: ZMod.unitsMap _ (Gamma0MapUnits ⟨γ, hγ⟩) = Gamma0MapUnits γ'_pkg
  exact unitsMap_Gamma0MapUnits_lift_eq_of_diag l N h_dvd γ hγ γ'_pkg j hdiag

/-- **Lowered character space membership for the cusp-form Case A bundle**
(T077 main result, cusp-form flavor). -/
theorem conductorTheoremCaseA_cuspForm_mem_cuspFormCharSpace
    (l N : ℕ) [NeZero l] [NeZero N] [NeZero (N / l)] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N) (h_fac : χ.FactorsThrough (N / l))
    (f : UpperHalfPlane → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    conductorTheoremCaseA_cuspForm l N h_dvd k χ h_fac f g hg_char hg_eq
        hf_period ∈
      cuspFormCharSpace k (loweredCharacter h_fac).toUnitHom := by
  rw [cuspFormCharSpace_iff_nebentypus]
  intro γ'_pkg
  -- ⇑(conductorTheoremCaseA_cuspForm ...) = f
  rw [conductorTheoremCaseA_cuspForm_apply]
  -- Identical proof shape to the modular-form case, using the
  -- ModularForm Case B side via cuspFormToModularForm bridge.
  -- Use the modular form ⇑g and its char-space membership.
  have hg_mod_char : cuspFormToModularForm g ∈ modFormCharSpace k χ.toUnitHom :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      k χ.toUnitHom g).mpr hg_char
  -- ⇑(cuspFormToModularForm g) = ⇑g = levelRaiseFun l k f.
  obtain ⟨i, j, γ, hγ, hfact, hdiag⟩ :=
    exists_T_levelRaiseConj_T_factor l N h_dvd γ'_pkg.val γ'_pkg.property
  rw [hfact]
  rw [conductor_slash_T_conj_eq l N h_dvd k χ f (cuspFormToModularForm g)
    hg_mod_char hg_eq hf_period i j γ hγ]
  congr 2
  rw [toUnitHom_loweredCharacter h_fac, MonoidHom.comp_apply]
  congr 1
  exact unitsMap_Gamma0MapUnits_lift_eq_of_diag l N h_dvd γ hγ γ'_pkg j hdiag

/-! ### Strengthened dichotomy with character-space membership (T077) -/

/-- **Strengthened modular-form dichotomy** (T077): same as
`conductor_theorem_dichotomy` but the Case A branch also asserts that
the lowered bundle lies in the lowered Nebentypus character space. -/
theorem conductor_theorem_dichotomy_strong
    (l N : ℕ) [NeZero l] [NeZero N] [NeZero (N / l)] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ modFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    (∃ h_fac : χ.FactorsThrough (N / l),
      ∃ F : ModularForm ((Gamma1 (N / l)).map (mapGL ℝ)) k,
        F ∈ modFormCharSpace k (loweredCharacter h_fac).toUnitHom ∧ ⇑F = f) ∨
    f = 0 := by
  classical
  by_cases h_fac : χ.FactorsThrough (N / l)
  · left
    refine ⟨h_fac, conductorTheoremCaseA_modularForm l N h_dvd k χ h_fac f g
      hg_char hg_eq hf_period, ?_, ?_⟩
    · exact conductorTheoremCaseA_modularForm_mem_modFormCharSpace l N h_dvd k χ
        h_fac f g hg_char hg_eq hf_period
    · exact conductorTheoremCaseA_modularForm_apply l N h_dvd k χ h_fac f g
        hg_char hg_eq hf_period
  · right
    exact conductorTheoremCaseB_vanishing l N h_dvd k χ h_fac f g hg_char hg_eq
      hf_period

/-- **Strengthened cusp-form dichotomy** (T077). -/
theorem conductor_theorem_dichotomy_cuspForm_strong
    (l N : ℕ) [NeZero l] [NeZero N] [NeZero (N / l)] (h_dvd : l ∣ N) (k : ℤ)
    (χ : DirichletCharacter ℂ N)
    (f : UpperHalfPlane → ℂ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ.toUnitHom)
    (hg_eq : ⇑g = levelRaiseFun l k f)
    (hf_period : f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f) :
    (∃ h_fac : χ.FactorsThrough (N / l),
      ∃ F : CuspForm ((Gamma1 (N / l)).map (mapGL ℝ)) k,
        F ∈ cuspFormCharSpace k (loweredCharacter h_fac).toUnitHom ∧ ⇑F = f) ∨
    f = 0 := by
  classical
  by_cases h_fac : χ.FactorsThrough (N / l)
  · left
    refine ⟨h_fac, conductorTheoremCaseA_cuspForm l N h_dvd k χ h_fac f g
      hg_char hg_eq hf_period, ?_, ?_⟩
    · exact conductorTheoremCaseA_cuspForm_mem_cuspFormCharSpace l N h_dvd k χ
        h_fac f g hg_char hg_eq hf_period
    · exact conductorTheoremCaseA_cuspForm_apply l N h_dvd k χ h_fac f g
        hg_char hg_eq hf_period
  · right
    have hg_mod_char : cuspFormToModularForm g ∈ modFormCharSpace k χ.toUnitHom :=
      (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        k χ.toUnitHom g).mpr hg_char
    exact conductorTheoremCaseB_vanishing l N h_dvd k χ h_fac f
      (cuspFormToModularForm g) hg_mod_char hg_eq hf_period

end HeckeRing.GL2

end

