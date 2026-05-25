/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.LevelRaise

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

private lemma dvd_lower_left_of_dvd_of_mem_Gamma0
    {l N : ℕ} (h_dvd : l ∣ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    (l : ℤ) ∣ γ.val 1 0 := by
  rw [Gamma0_mem] at hγ
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h_dvd)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ)

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
  rwa [hg_eq, slash_mapGL_levelRaiseFun] at h_neb

/-- Auxiliary: the scalar multiplication commutes with the level-raise operator.
For `c : ℂ` and `f : ℍ → ℂ`, `c • levelRaiseFun l k f = levelRaiseFun l k (c • f)`.
The slash action by `α_l` (positive determinant, σ trivial) commutes with the
complex scalar action. -/
lemma smul_levelRaiseFun (l : ℕ) [NeZero l] (k : ℤ) (c : ℂ)
    (f : UpperHalfPlane → ℂ) :
    c • levelRaiseFun l k f = levelRaiseFun l k (c • f) := by
  funext τ; simp [levelRaiseFun_apply, smul_eq_mul]

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
    f = fun τ ↦ g ((levelRaiseMatrix l)⁻¹ • τ) :=
  funext (fun_eq_apply_levelRaiseMatrix_inv_smul l k f g hg)

/-- Positive determinant of `(levelRaiseMatrix l)⁻¹`: the inverse has det
`1 / l > 0`. Used to invoke `UpperHalfPlane.mdifferentiable_smul` for the
inverse action. -/
lemma levelRaiseMatrix_inv_det_pos (l : ℕ) [NeZero l] :
    (0 : ℝ) < (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l)⁻¹ : ℝ) := by
  rw [show (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l)⁻¹ : ℝˣ) =
      (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l))⁻¹ from
    map_inv Matrix.GeneralLinearGroup.det _, Units.val_inv_eq_inv_val]
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

private def slashStabilizerOfFun (k : ℤ) (f : UpperHalfPlane → ℂ) :
    Subgroup SL(2, ℤ) where
  carrier := { γ | f ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = f }
  one_mem' := by
    show f ∣[k] (mapGL ℝ (1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = f
    rw [map_one, SlashAction.slash_one]
  mul_mem' := fun {a b} ha hb ↦ by
    show f ∣[k] (mapGL ℝ (a * b) : GL (Fin 2) ℝ) = f
    rw [map_mul, SlashAction.slash_mul, ha, hb]
  inv_mem' := fun {a} ha ↦ by
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
  rw [show mapGL ℝ (ModularGroup.T ^ i * gtilde * ModularGroup.T ^ j) =
        mapGL ℝ (ModularGroup.T ^ i) * mapGL ℝ gtilde * mapGL ℝ (ModularGroup.T ^ j) from
      by simp [map_mul],
    SlashAction.slash_mul, SlashAction.slash_mul,
    slash_T_zpow_eq_self_of_slash_T_eq k f hf_period i,
    conductor_slash_eq l N h_dvd k χ f g hg_char hg_eq γ hγ]
  have hσ_T : UpperHalfPlane.σ
      (mapGL ℝ (ModularGroup.T ^ j) : GL (Fin 2) ℝ) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos]
    show (0 : ℝ) < (Matrix.GeneralLinearGroup.det
      (mapGL ℝ (ModularGroup.T ^ j))).val
    rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num
  rw [ModularForm.smul_slash, hσ_T, RingHom.id_apply,
    slash_T_zpow_eq_self_of_slash_T_eq k f hf_period j]

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
  obtain ⟨i, j, γ, hγ, hfact, hdiag⟩ :=
    exists_T_levelRaiseConj_T_factor l N h_dvd δ (Gamma1_in_Gamma0 _ hδ)
  rw [hfact, conductor_slash_T_conj_eq l N h_dvd k χ f g hg_char hg_eq
    hf_period i j γ hγ]
  suffices h_char : χ.toUnitHom (Gamma0MapUnits ⟨γ, hγ⟩) = 1 by
    rw [h_char, Units.val_one, one_smul]
  rw [toUnitHom_loweredCharacter h_fac, MonoidHom.comp_apply]
  have h_red : ZMod.unitsMap h_fac.dvd (Gamma0MapUnits ⟨γ, hγ⟩) = 1 := by
    apply Units.ext
    simp only [Units.val_one, ZMod.unitsMap_val, Gamma0MapUnits_val]
    rw [show Gamma0Map N ⟨γ, hγ⟩ = ((γ.val 1 1 : ℤ) : ZMod N) from rfl,
      ZMod.cast_intCast h_fac.dvd, hdiag]
    push_cast
    rw [Gamma1_mem] at hδ
    obtain ⟨_, hd_one, hc_zero⟩ := hδ
    rw [hd_one, hc_zero, zero_mul, sub_zero]
  rw [h_red, map_one]

/-- The action of `(levelRaiseMatrix l)⁻¹` on `ℍ` scales the underlying
ℂ-coordinate by `1/l`: `(α_l⁻¹ • z).coe = z.coe / l`. Derived from the
diagonal action of `α_l` (`coe_levelRaiseMatrix_smul`) by inverting
`α_l • (α_l⁻¹ • z) = z`. -/
lemma coe_levelRaiseMatrix_inv_smul (l : ℕ) [NeZero l] (z : UpperHalfPlane) :
    (((levelRaiseMatrix l)⁻¹ • z : UpperHalfPlane) : ℂ) = (↑z : ℂ) / (l : ℂ) := by
  have h_unit : (levelRaiseMatrix l) • ((levelRaiseMatrix l)⁻¹ • z) = z := by
    rw [smul_smul, mul_inv_cancel, one_smul]
  have h_coe_eq : (((levelRaiseMatrix l) • ((levelRaiseMatrix l)⁻¹ • z) :
      UpperHalfPlane) : ℂ) = ((z : UpperHalfPlane) : ℂ) := by rw [h_unit]
  rw [coe_levelRaiseMatrix_smul] at h_coe_eq
  rwa [eq_div_iff (Nat.cast_ne_zero.mpr (NeZero.ne l) : (l : ℂ) ≠ 0), mul_comm]

/-- The imaginary part of `(α_l⁻¹ • z)` is `z.im / l`. -/
lemma im_levelRaiseMatrix_inv_smul (l : ℕ) [NeZero l] (z : UpperHalfPlane) :
    ((levelRaiseMatrix l)⁻¹ • z : UpperHalfPlane).im = z.im / (l : ℝ) := by
  show (((levelRaiseMatrix l)⁻¹ • z : UpperHalfPlane) : ℂ).im = z.im / (l : ℝ)
  rw [coe_levelRaiseMatrix_inv_smul]
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
  refine ⟨M, A * (l : ℝ), fun z' hz' ↦ ?_⟩
  rw [fun_eq_apply_levelRaiseMatrix_inv_smul l k f g hg_eq z']
  apply hbound
  rw [im_levelRaiseMatrix_inv_smul]
  rwa [le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_neZero l))]

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
    ← SlashAction.slash_mul,
    show (levelRaiseMatrix l : GL (Fin 2) ℝ) * (levelRaiseMatrix l)⁻¹ = 1
      from mul_inv_cancel _, SlashAction.slash_one]

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
  have hf_eq : f = ((l : ℂ) ^ (k - 1)) •
      (g ∣[k] ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ)) := by
    rw [slash_inv_eq_smul_of_levelRaiseFun_eq l k f g hg_eq, smul_smul,
      ← zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne l) : (l : ℂ) ≠ 0),
      show k - 1 + (1 - k) = 0 from by ring, zpow_zero, one_smul]
  conv_lhs => rw [hf_eq]
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
  rw [slash_eq_of_levelRaiseFun_eq l k f g hg_eq A,
    UpperHalfPlane.isBoundedAtImInfty_iff, UpperHalfPlane.isBoundedAtImInfty_iff]
  constructor
  · rintro ⟨M, A_im, hbound⟩
    refine ⟨M / ‖((l : ℂ) ^ (k - 1))‖, A_im, fun τ hτ ↦ ?_⟩
    have h := hbound τ hτ
    rw [Pi.smul_apply, smul_eq_mul, norm_mul] at h
    rwa [le_div_iff₀ (by rw [norm_pos_iff]; exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne l))), mul_comm]
  · rintro ⟨M, A_im, hbound⟩
    refine ⟨‖((l : ℂ) ^ (k - 1))‖ * M, A_im, fun τ hτ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound τ hτ) (norm_nonneg _)

open OnePoint in
private lemma levelRaiseMatrix_inv_apply_one_zero (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 1 0 = 0 := by
  show ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val 1 0 = 0
  rw [Matrix.GeneralLinearGroup.coe_inv]
  show (((levelRaiseMatrix l : GL (Fin 2) ℝ)).val)⁻¹ 1 0 = 0
  rw [Matrix.inv_def]
  show (Ring.inverse ((levelRaiseMatrix l : GL (Fin 2) ℝ).val).det •
      ((levelRaiseMatrix l : GL (Fin 2) ℝ).val).adjugate) 1 0 = 0
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

open OnePoint in
private lemma levelRaiseMatrix_inv_apply_one_one (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 1 1 = 1 := by
  show ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val 1 1 = 1
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

open OnePoint in
private lemma levelRaiseMatrix_inv_apply_zero_zero (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 0 0 = (l : ℝ)⁻¹ := by
  show ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val 0 0 = (l : ℝ)⁻¹
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

open OnePoint in
private lemma levelRaiseMatrix_inv_apply_zero_one (l : ℕ) [NeZero l] :
    ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) 0 1 = 0 := by
  show ((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ).val 0 1 = 0
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.smul_apply]

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

private lemma gcd_levelRaise_first_col_ne_zero (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0) : ℤ) ≠ 0 := by
  intro hgcd
  rw [gcd_eq_zero_iff] at hgcd
  obtain ⟨ha, hlc⟩ := hgcd
  rcases mul_eq_zero.mp hlc with h | h
  · exact Nat.cast_ne_zero.mpr (NeZero.ne l) h
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

private lemma cuspWitnessLevelRaiseInv_first_col (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (cuspWitnessLevelRaiseInv l A) 0 0 =
        A.val 0 0 / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) ∧
    (cuspWitnessLevelRaiseInv l A) 1 0 =
        ((l : ℤ) * A.val 1 0) / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) :=
  Classical.choose_spec
    ((isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
      (gcd_levelRaise_first_col_ne_zero l A)).exists_SL2_col 0)

private lemma mapGL_cuspWitnessLevelRaiseInv_apply_one_zero
    (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ) 1 0 =
      ((((l : ℤ) * A.val 1 0) / (gcd (A.val 0 0) ((l : ℤ) * A.val 1 0)) : ℤ) : ℝ) := by
  show (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ).val 1 0 = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  show (algebraMap ℤ ℝ) ((cuspWitnessLevelRaiseInv l A).val 1 0) = _
  rw [(cuspWitnessLevelRaiseInv_first_col l A).2]
  simp

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
private lemma mapGL_cuspWitnessLevelRaiseInv_smul_infty_eq
    (l : ℕ) [NeZero l] (A : SL(2, ℤ)) :
    (mapGL ℝ (cuspWitnessLevelRaiseInv l A) : GL (Fin 2) ℝ) • (∞ : OnePoint ℝ) =
      (((levelRaiseMatrix l)⁻¹ : GL (Fin 2) ℝ) * (mapGL ℝ A : GL (Fin 2) ℝ)) • ∞ := by
  set d : ℤ := gcd (A.val 0 0) ((l : ℤ) * A.val 1 0) with hd_def
  have hd_ne : d ≠ 0 := gcd_levelRaise_first_col_ne_zero l A
  have hd_real_ne : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd_ne
  rw [OnePoint.smul_infty_eq_ite, OnePoint.smul_infty_eq_ite,
    mapGL_cuspWitnessLevelRaiseInv_apply_one_zero,
    mapGL_cuspWitnessLevelRaiseInv_apply_zero_zero,
    levelRaiseMatrix_inv_mul_mapGL_apply_one_zero,
    levelRaiseMatrix_inv_mul_mapGL_apply_zero_zero]
  have h_int_div_a : (((A.val 0 0) / d : ℤ) : ℝ) = (A.val 0 0 : ℝ) / (d : ℝ) :=
    Int.cast_div (gcd_dvd_left _ _) hd_real_ne
  have h_int_div_lc : ((((l : ℤ) * A.val 1 0) / d : ℤ) : ℝ) =
      ((l : ℝ) * A.val 1 0) / (d : ℝ) := by
    rw [Int.cast_div (gcd_dvd_right _ _) hd_real_ne]; push_cast; ring
  rw [h_int_div_a, h_int_div_lc]
  by_cases hc : (A.val 1 0 : ℝ) = 0
  · have h_lc_zero : ((l : ℝ) * (A.val 1 0 : ℝ)) / (d : ℝ) = 0 := by
      rw [hc, mul_zero, zero_div]
    rw [if_pos h_lc_zero, if_pos hc]
  · rw [if_neg (div_ne_zero (mul_ne_zero
        (Nat.cast_ne_zero.mpr (NeZero.ne l)) hc) hd_real_ne), if_neg hc]
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
  exact ModularFormClass.bdd_at_cusps g
    (isCusp_levelRaiseMatrix_inv_mul_mapGL_smul_infty l A ((Gamma1 N).map (mapGL ℝ))) _ rfl

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
  haveI : NeZero (N / l) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) h_dvd)
    (Nat.pos_of_neZero l)).ne'⟩
  have hc_SL : IsCusp c 𝒮ℒ :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
  rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc_SL]
  obtain ⟨γ, hγ⟩ := isCusp_SL2Z_iff'.mp hc_SL
  refine ⟨γ, hγ.symm, ?_⟩
  rw [ModularForm.SL_slash]
  exact isBoundedAtImInfty_slash_mapGL_of_levelRaiseFun_eq l N k f g hg_eq γ

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
  refine ⟨A * (l : ℝ), fun z' hz' ↦ ?_⟩
  rw [fun_eq_apply_levelRaiseMatrix_inv_smul l k f g hg_eq z']
  apply hbound
  rw [im_levelRaiseMatrix_inv_smul]
  rwa [le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_neZero l))]

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
  have hc_norm_pos : 0 < ‖((l : ℂ) ^ (k - 1))‖ := by
    rw [norm_pos_iff]; exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne l))
  rw [UpperHalfPlane.isZeroAtImInfty_iff, UpperHalfPlane.isZeroAtImInfty_iff]
  constructor
  · intro h ε hε
    obtain ⟨A_im, hbound⟩ := h (ε * ‖((l : ℂ) ^ (k - 1))‖)
      (mul_pos hε hc_norm_pos)
    refine ⟨A_im, fun τ hτ ↦ ?_⟩
    have h := hbound τ hτ
    rw [Pi.smul_apply, smul_eq_mul, norm_mul] at h
    rwa [mul_comm, ← le_div_iff₀ hc_norm_pos,
      mul_div_assoc, div_self hc_norm_pos.ne', mul_one] at h
  · intro h ε hε
    obtain ⟨A_im, hbound⟩ := h (ε / ‖((l : ℂ) ^ (k - 1))‖)
      (div_pos hε hc_norm_pos)
    refine ⟨A_im, fun τ hτ ↦ ?_⟩
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
  exact CuspFormClass.zero_at_cusps g
    (isCusp_levelRaiseMatrix_inv_mul_mapGL_smul_infty l A ((Gamma1 N).map (mapGL ℝ))) _ rfl

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
  haveI : NeZero (N / l) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) h_dvd)
    (Nat.pos_of_neZero l)).ne'⟩
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
  bdd_at_cusps' hc := fun M hM ↦
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
    exact conductor_slash_eq_self_of_mem_Gamma1_div l N h_dvd k χ h_fac f
      (cuspFormToModularForm g)
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        k χ.toUnitHom g).mpr hg_char) hg_eq hf_period δ hδ_mem
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
  · exact hu_chi ∘ MonoidHom.mem_ker.mpr

/-- For `l ∣ N`, the integer cast factors as `N = l * (N / l)`. -/
private lemma natCast_eq_mul_natCast_div {l N : ℕ} (h_dvd : l ∣ N) :
    (N : ℤ) = (l : ℤ) * ((N / l : ℕ) : ℤ) := by
  rw [mul_comm]; exact_mod_cast (Nat.div_mul_cancel h_dvd).symm

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
  have hN_dvd_c : (N : ℤ) ∣ γ.val 1 0 := by
    rw [Gamma0_mem] at hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have hNl_dvd_N : ((N / l : ℕ) : ℤ) ∣ (N : ℤ) := by
    refine ⟨(l : ℤ), ?_⟩
    rw [show ((N : ℕ) : ℤ) = (((N / l) * l : ℕ) : ℤ) from by rw [Nat.div_mul_cancel h_dvd],
      Nat.cast_mul]
  have h10_mod : ((γ.val 1 0 : ℤ) : ZMod (N / l)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans hNl_dvd_N hN_dvd_c)
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · show (((gtilde 0 0 : ℤ)) : ZMod (N / l)) = 1
    rw [show ((gtilde : SL(2, ℤ)) 0 0 : ℤ) = gtilde.val 0 0 from rfl, hgtilde_eq00]
    have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact γ.property
    have hdet_mod : ((γ.val 0 0 : ℤ) : ZMod (N/l)) * ((γ.val 1 1 : ℤ) : ZMod (N/l)) -
        ((γ.val 0 1 : ℤ) : ZMod (N/l)) * ((γ.val 1 0 : ℤ) : ZMod (N/l)) = 1 := by
      have := congr_arg (fun x : ℤ ↦ ((x : ℤ) : ZMod (N/l))) hdet
      push_cast at this
      simpa using this
    rwa [hγ_ker, mul_one, h10_mod, mul_zero, sub_zero] at hdet_mod
  · show (((gtilde 1 1 : ℤ)) : ZMod (N / l)) = 1
    rwa [show ((gtilde : SL(2, ℤ)) 1 1 : ℤ) = gtilde.val 1 1 from rfl, hgtilde_eq11]
  · show (((gtilde 1 0 : ℤ)) : ZMod (N / l)) = 0
    rw [show ((gtilde : SL(2, ℤ)) 1 0 : ℤ) = gtilde.val 1 0 from rfl, hgtilde_eq10,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨m, hm⟩ := hN_dvd_c
    rw [hm, natCast_eq_mul_natCast_div h_dvd,
      show ((l : ℤ) * ((N / l : ℕ) : ℤ)) * m = (l : ℤ) * (((N / l : ℕ) : ℤ) * m) from by ring,
      Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne l))]
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
  have hγu_ker : ((γ_u.val 1 1 : ℤ) : ZMod (N / l)) = 1 := by
    have h_val_eq : ((γ_u.val 1 1 : ℤ) : ZMod N) = (u : ZMod N) := by
      have h1 : Gamma0Map N gu = ((γ_u.val 1 1 : ℤ) : ZMod N) := rfl
      rw [← h1, ← Gamma0MapUnits_val gu, hgu_eq]
    have h_u_red : (ZMod.cast (u : ZMod N) : ZMod (N / l)) = 1 := by
      simpa [ZMod.unitsMap_val] using congr_arg Units.val hu_ker
    rw [← ZMod.cast_intCast hNl_dvd_N (γ_u.val 1 1) (R := ZMod (N / l)),
      h_val_eq, h_u_red]
  set delta := levelRaiseConjOfDvd l γ_u
    (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd hγu_mem)
  refine ⟨delta,
    levelRaiseConjOfDvd_mem_Gamma1_div_of_mem_ker l N h_dvd hγu_mem hγu_ker,
    (χ.toUnitHom (Gamma0MapUnits ⟨γ_u, hγu_mem⟩) : ℂ), ?_, ?_⟩
  · intro h_eq
    rw [hgu_eq] at h_eq
    exact hu_chi (Units.ext h_eq)
  · exact conductor_slash_eq l N h_dvd k χ f g hg_char hg_eq γ_u hγu_mem

/-- **Algebraic two-multiplier contradiction.** If `f ∣[k] M` is BOTH `c₁ • f`
AND `c₂ • f` for two distinct scalars, then `f = 0`. This captures the
algebraic core of the Case B vanishing argument: when two factorizations of
the same matrix produce different `χ` multipliers, the underlying function
must vanish. -/
lemma fun_eq_zero_of_two_multipliers (k : ℤ) (f : UpperHalfPlane → ℂ)
    (M : GL (Fin 2) ℝ) {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (h₁ : f ∣[k] M = c₁ • f) (h₂ : f ∣[k] M = c₂ • f) :
    f = 0 := by
  have h_diff : (c₁ - c₂) • f = 0 := by
    rw [sub_smul, h₁.symm.trans h₂, sub_self]
  rcases smul_eq_zero.mp h_diff with hc | hf
  · exact absurd hc (sub_ne_zero.mpr hne)
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
  have h_ae : ((a * e : ℤ) : ZMod N) = 1 := by
    show (((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ)) : ℤ) : ZMod N) = 1
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have h_dvd : (N : ℤ) ∣ (a * e - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [show ((a : ZMod N) * (e : ZMod N) - 1 : ZMod N) =
        ((a * e : ℤ) : ZMod N) - 1 from by push_cast; ring, h_ae]
    ring
  let b : ℤ := (a * e - 1) / (N : ℤ)
  refine ⟨⟨!![a, b; (N : ℤ), e], ?det⟩, ?gamma0⟩
  · rw [Matrix.det_fin_two_of]
    show a * e - b * (N : ℤ) = 1
    linarith [Int.ediv_mul_cancel h_dvd]
  · rw [Gamma0_mem]
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
  obtain ⟨u, hu_ker, hu_chi⟩ :=
    exists_unit_of_not_factorsThrough ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ h_not_fac
  refine ⟨u, hu_ker, hu_chi, gamma0LiftLowerLeftN_lower_left N u, ?_⟩
  have h_slash := conductor_slash_eq l N h_dvd k χ f g hg_char hg_eq
    (gamma0LiftLowerLeftN N u : SL(2, ℤ)) (gamma0LiftLowerLeftN N u).property
  rwa [show Gamma0MapUnits ⟨(gamma0LiftLowerLeftN N u : SL(2, ℤ)),
      (gamma0LiftLowerLeftN N u).property⟩ = u from
    gamma0LiftLowerLeftN_Gamma0MapUnits N u] at h_slash

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
    have h1 : (l : ℤ) ∣ -(- j * (a₀ - i * ((N / l : ℕ) : ℤ)) + l * b₀ - i * e₀) :=
      dvd_neg.mpr h
    have h2 : (-(- j * (a₀ - i * ((N / l : ℕ) : ℤ)) + l * b₀ - i * e₀)) =
        (i * e₀ + j * a₀ - i * j * ((N / l : ℕ) : ℤ)) - l * b₀ := by ring
    rw [h2] at h1
    have hl_lb₀ : (l : ℤ) ∣ l * b₀ := ⟨b₀, rfl⟩
    simpa using dvd_add h1 hl_lb₀
  · intro h
    have hl_lb₀ : (l : ℤ) ∣ l * b₀ := ⟨b₀, rfl⟩
    have : (l : ℤ) ∣ -((i * e₀ + j * a₀ - i * j * ((N / l : ℕ) : ℤ)) - l * b₀) :=
      dvd_neg.mpr (dvd_sub h hl_lb₀)
    have h2 : -((i * e₀ + j * a₀ - i * j * ((N / l : ℕ) : ℤ)) - l * b₀) =
        (- j * (a₀ - i * ((N / l : ℕ) : ℤ)) + l * b₀ - i * e₀) := by ring
    rwa [h2] at this

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
  exact hv_chi <| mul_left_cancel <| show χ.toUnitHom u * χ.toUnitHom v = χ.toUnitHom u * 1 by
    rw [← map_mul, h, mul_one]

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
  have h_cast_one : ZMod.castHom ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩
      (ZMod (N / l)) (v : ZMod N) = 1 := by
    have hh := congr_arg Units.val hv_ker
    rwa [ZMod.unitsMap_val, Units.val_one] at hh
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val (v : ZMod N),
    show (ZMod.cast ((v : ZMod N) : ZMod N) : ZMod (N / l)) =
      ZMod.castHom ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ (ZMod (N / l)) (v : ZMod N) from rfl,
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
  · rw [map_mul, hv_ker, mul_one]
  · exact hv_chi

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
    rwa [ZMod.unitsMap_val, ZMod.unitsMap_val] at hh
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val (u : ZMod N), ZMod.natCast_val (u' : ZMod N),
    show (ZMod.cast ((u : ZMod N) : ZMod N) : ZMod (N / l)) =
        ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u : ZMod N) from rfl,
    show (ZMod.cast ((u' : ZMod N) : ZMod N) : ZMod (N / l)) =
        ZMod.castHom hNl_dvd_N (ZMod (N / l)) (u' : ZMod N) from rfl,
    h_cast_eq]
  ring

/-- The `(0, 1)` entry of the controlled lift `gamma0LiftLowerLeftN N u` is
the Bezout coefficient `b = (a*e - 1) / N` (where `a = u⁻¹.val.val`,
`e = u.val.val`). Proved by direct unfolding. -/
@[simp]
lemma gamma0LiftLowerLeftN_upper_right (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 1 : ℤ) =
      (((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) /
        (N : ℤ) := rfl

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
  · lia
  · apply mul_left_cancel₀ hNl
    linear_combination -h_det + h_det' + (-e' - Nl * j) * h_i + (-a) * h_j
  · lia

private lemma N_dvd_inv_val_mul_val_sub_one (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (N : ℤ) ∣ (((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have h_unit : u⁻¹.val * u.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h_unit]
  ring

private lemma controlled_lift_det_identity (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) -
      ((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) / (N : ℤ)) *
        (N : ℤ) = 1 := by
  linarith [Int.ediv_mul_cancel (N_dvd_inv_val_mul_val_sub_one N u)]

/-- The underlying matrix of the level-raising conjugate of the controlled lift
`gamma0LiftLowerLeftN N u`: it is `!![a, l*b; N/l, e]` where `a, b, e` are the
entries of `gamma0LiftLowerLeftN N u`. -/
private lemma levelRaiseConjOfDvd_gamma0LiftLowerLeftN_val
    (l N : ℕ) [NeZero l] [NeZero N] (h_dvd : l ∣ N) (u : (ZMod N)ˣ) :
    (levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u : SL(2, ℤ))
      (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
        (gamma0LiftLowerLeftN N u).property)).val =
      (!![((u⁻¹.val : ZMod N).val : ℤ),
          (l : ℤ) * ((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) /
            (N : ℤ));
          ((N / l : ℕ) : ℤ), ((u.val : ZMod N).val : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) := by
  show (Matrix.of !![(gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 0,
      (l : ℤ) * (gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 0 1;
      (gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 0 / l,
      (gamma0LiftLowerLeftN N u : SL(2, ℤ)).val 1 1] : Matrix _ _ ℤ) =
    !![((u⁻¹.val : ZMod N).val : ℤ),
        (l : ℤ) * ((((u⁻¹.val : ZMod N).val : ℤ) * ((u.val : ZMod N).val : ℤ) - 1) /
          (N : ℤ));
        ((N / l : ℕ) : ℤ), ((u.val : ZMod N).val : ℤ)]
  have h_div_eq : (N : ℤ) / (l : ℤ) = ((N / l : ℕ) : ℤ) := by
    rw [natCast_eq_mul_natCast_div h_dvd,
      Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne l))]
  ext p q; fin_cases p <;> fin_cases q <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, gamma0LiftLowerLeftN_upper_left,
      gamma0LiftLowerLeftN_upper_right, gamma0LiftLowerLeftN_lower_left,
      gamma0LiftLowerLeftN_lower_right, h_div_eq]

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
  obtain ⟨u', hu'_coset, hu'_chi⟩ :=
    exists_alt_unit_in_coset_with_char_separation
      ⟨l, (Nat.div_mul_cancel h_dvd).symm⟩ h_not_fac u
  set a₀ : ℤ := ((u⁻¹.val : ZMod N).val : ℤ)
  set e₀ : ℤ := ((u.val : ZMod N).val : ℤ)
  set a₀' : ℤ := ((u'⁻¹.val : ZMod N).val : ℤ)
  set e₀' : ℤ := ((u'.val : ZMod N).val : ℤ)
  set b₀ : ℤ := (a₀ * e₀ - 1) / (N : ℤ)
  set b₀' : ℤ := (a₀' * e₀' - 1) / (N : ℤ)
  set Nl : ℤ := ((N / l : ℕ) : ℤ)
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
  have hN_eq : (N : ℤ) = (l : ℤ) * Nl := natCast_eq_mul_natCast_div h_dvd
  have hNl_ne : Nl ≠ 0 :=
    show ((N / l : ℕ) : ℤ) ≠ 0 from by
      exact_mod_cast (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) h_dvd)
        (Nat.pos_of_neZero l)).ne'
  have h_det_u : a₀ * e₀ - b₀ * ((l : ℤ) * Nl) = 1 := by
    rw [← hN_eq]; exact controlled_lift_det_identity N u
  have h_det_u' : a₀' * e₀' - b₀' * ((l : ℤ) * Nl) = 1 := by
    rw [← hN_eq]; exact controlled_lift_det_identity N u'
  have h_mat_id :
      (!![a₀, (l : ℤ) * b₀; Nl, e₀] : Matrix (Fin 2) (Fin 2) ℤ) =
        !![(1 : ℤ), i; 0, 1] * !![a₀', (l : ℤ) * b₀'; Nl, e₀'] *
          !![(1 : ℤ), j; 0, 1] :=
    t_factor_matrix_identity hNl_ne h_i_eq h_j_eq h_det_u h_det_u'
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow]
  have h_lhs_val : (levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u : SL(2, ℤ))
      (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
        (gamma0LiftLowerLeftN N u).property)).val =
      (!![a₀, (l : ℤ) * b₀; Nl, e₀] : Matrix (Fin 2) (Fin 2) ℤ) :=
    levelRaiseConjOfDvd_gamma0LiftLowerLeftN_val l N h_dvd u
  have h_rhs_val : (levelRaiseConjOfDvd l (gamma0LiftLowerLeftN N u' : SL(2, ℤ))
      (dvd_lower_left_of_dvd_of_mem_Gamma0 h_dvd
        (gamma0LiftLowerLeftN N u').property)).val =
      (!![a₀', (l : ℤ) * b₀'; Nl, e₀'] : Matrix (Fin 2) (Fin 2) ℤ) :=
    levelRaiseConjOfDvd_gamma0LiftLowerLeftN_val l N h_dvd u'
  rwa [h_lhs_val, h_rhs_val]

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
  obtain ⟨u, _, _, _, h_slash⟩ :=
    case_B_slash_relation_with_controlled_lift l N h_dvd k χ h_not_fac f g
      hg_char hg_eq
  obtain ⟨i, j, u', hu'_chi, h_mat_id⟩ :=
    exists_T_factor_with_char_separation l N h_dvd χ h_not_fac u
  have h_slash_alt :=
    conductor_slash_T_conj_eq l N h_dvd k χ f g hg_char hg_eq hf_period
      i j (gamma0LiftLowerLeftN N u' : SL(2, ℤ))
      (gamma0LiftLowerLeftN N u').property
  rw [gamma0LiftLowerLeftN_Gamma0MapUnits, ← h_mat_id] at h_slash_alt
  exact fun_eq_zero_of_two_multipliers k f _
    (fun h ↦ hu'_chi.symm (Units.ext h)) h_slash h_slash_alt

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
    exact conductorTheoremCaseB_vanishing l N h_dvd k χ h_fac f
      (cuspFormToModularForm g)
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        k χ.toUnitHom g).mpr hg_char) hg_eq hf_period

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
    have hγ' := γ'_pkg.property
    rwa [Gamma0_mem] at hγ'
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
  obtain ⟨i, j, γ, hγ, hfact, hdiag⟩ :=
    exists_T_levelRaiseConj_T_factor l N h_dvd γ'_pkg.val γ'_pkg.property
  rw [hfact, conductor_slash_T_conj_eq l N h_dvd k χ f g hg_char hg_eq hf_period i j γ hγ]
  congr 2
  rw [toUnitHom_loweredCharacter h_fac, MonoidHom.comp_apply]
  congr 1
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
  rw [conductorTheoremCaseA_cuspForm_apply]
  obtain ⟨i, j, γ, hγ, hfact, hdiag⟩ :=
    exists_T_levelRaiseConj_T_factor l N h_dvd γ'_pkg.val γ'_pkg.property
  rw [hfact, conductor_slash_T_conj_eq l N h_dvd k χ f (cuspFormToModularForm g)
    ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      k χ.toUnitHom g).mpr hg_char) hg_eq hf_period i j γ hγ]
  congr 2
  rw [toUnitHom_loweredCharacter h_fac, MonoidHom.comp_apply]
  congr 1
  exact unitsMap_Gamma0MapUnits_lift_eq_of_diag l N h_dvd γ hγ γ'_pkg j hdiag

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
    exact conductorTheoremCaseB_vanishing l N h_dvd k χ h_fac f
      (cuspFormToModularForm g)
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        k χ.toUnitHom g).mpr hg_char) hg_eq hf_period

end HeckeRing.GL2

end

