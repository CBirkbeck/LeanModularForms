# /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/CongruenceSubgrps.lean

## noncomputable def `Subgroup.width`
- **Type**: `(Γ : Subgroup SL(2, ℤ)) : ℕ`, defined as
  `Subgroup.relIndex Γ (.zpowers ModularGroup.T)`.
- **What**: The "width" of the cusp `∞` for a subgroup `Γ` of `SL(2, ℤ)`:
  the least `n > 0` such that `[1, n; 0, 1] = T^n ∈ Γ`. Encoded as the
  relative index of `Γ` inside `⟨T⟩`.
- **How**: Direct definition via `Subgroup.relIndex`.
- **Hypotheses**: n/a (definition).
- **Uses-from-project**: mathlib (`Mathlib.NumberTheory.ModularForms.CongruenceSubgroups`,
  `Subgroup.relIndex`, `ModularGroup.T`).
- **Used by**: `width_ne_zero`, `T_pow_width_mem`, `T_zpow_mem_iff`,
  `T_pow_mem_iff`, `Gamma_width`, `ModularGroup_T_pow_mem_Gamma` (locally);
  every modular-form file working with cusp-widths (e.g. `Identities`,
  `IsBoundedAtImInfty`).
- **Visibility**: public `noncomputable def`; namespace `Subgroup`.
- **Lines**: 38-39.

## lemma `Subgroup.width_ne_zero`
- **Type**: `[Γ.FiniteIndex] → Γ.width ≠ 0`.
- **What**: A finite-index subgroup of `SL(2, ℤ)` has positive cusp-width.
- **How**: `FiniteIndex.index_ne_zero`.
- **Hypotheses**: `Γ.FiniteIndex`.
- **Uses-from-project**: `Subgroup.width`.
- **Used by**: Callers needing nonzero width for divisibility arguments.
- **Visibility**: public; namespace `Subgroup`.
- **Lines**: 41-42.

## lemma `Subgroup.T_pow_width_mem`
- **Type**: `T ^ Γ.width ∈ Γ`.
- **What**: `T^width` lies in `Γ` — the defining property of the width.
- **How**: Sets `CommGroup (zpowers T)` via `IsCyclic.commGroup`, then
  invokes `(Γ.subgroupOf (zpowers T)).pow_index_mem ⟨_, mem_zpowers _⟩`.
- **Hypotheses**: none beyond `Γ : Subgroup SL(2, ℤ)`.
- **Uses-from-project**: `Subgroup.width`.
- **Used by**: Callers needing that the width power of `T` is in `Γ`.
- **Visibility**: public; namespace `Subgroup`.
- **Lines**: 44-46.

## lemma `Subgroup.T_zpow_mem_iff`
- **Type**: `{n : ℤ} → T ^ n ∈ Γ ↔ ↑Γ.width ∣ n`.
- **What**: The integers `n` with `T^n ∈ Γ` are precisely the multiples of
  `Γ.width`.
- **How**: Let `A := (Γ.comap (zpowersHom _ T)).toAddSubgroup'` and pick
  `m` with `A = AddSubgroup.zmultiples m` via `Int.subgroup_cyclic`. Two
  identities `(Γ.comap _).index = Γ.width` (from `Γ.index_comap`) and
  `Γ.width = A.index` (from `A.index_toSubgroup`) align the index counters.
  The membership chain `T^n ∈ Γ ↔ n ∈ A ↔ ↑A.index ∣ n` is then closed by
  `AddSubgroup.zmultiples_eq_closure`, `Int.mem_zmultiples_iff`,
  `Int.index_zmultiples`, and `Int.natAbs_dvd`.
- **Hypotheses**: none.
- **Uses-from-project**: `Subgroup.width`.
- **Used by**: `Subgroup.T_pow_mem_iff`, `Subgroup.Gamma_width`,
  `ModularGroup_T_pow_mem_Gamma`.
- **Visibility**: public; namespace `Subgroup`.
- **Lines**: 49-55.

## lemma `Subgroup.T_pow_mem_iff`
- **Type**: `(n : ℕ) → T ^ n ∈ Γ ↔ Γ.width ∣ n`.
- **What**: Same as `T_zpow_mem_iff` but for natural-number exponents.
- **How**: `simpa [Int.natCast_dvd_natCast]` from `T_zpow_mem_iff` with
  `n` coerced to `ℤ`.
- **Hypotheses**: none.
- **Uses-from-project**: `Subgroup.T_zpow_mem_iff`.
- **Used by**: `Subgroup.Gamma_width` (locally).
- **Visibility**: public; namespace `Subgroup`.
- **Lines**: 59-60.

## simp lemma `Subgroup.Gamma_width`
- **Type**: `Γ(N).width = N`.
- **What**: For the principal congruence subgroup `Γ(N) ⊆ SL(2, ℤ)`, the
  cusp-width equals `N`.
- **How**: `simp` chain with `← Nat.dvd_right_iff_eq`, `← T_pow_mem_iff`,
  `← zpow_natCast`, `ModularGroup.coe_T_zpow`, and
  `ZMod.natCast_eq_zero_iff`.
- **Hypotheses**: takes `N : ℕ` as an explicit argument (via `variable (N : ℕ)`).
- **Uses-from-project**: `Subgroup.T_pow_mem_iff` (and so transitively
  `width`).
- **Used by**: `ModularGroup_T_pow_mem_Gamma` (locally); modular-form
  files needing `Γ(N).width = N` (e.g. `IsBoundedAtImInfty`, `Identities`).
- **Visibility**: public `@[simp] lemma`; namespace `Subgroup`.
- **Lines**: 64.

## lemma `Subgroup.ModularGroup_T_pow_mem_Gamma`
- **Type**: `(N M : ℤ) (hNM : N ∣ M) → T ^ M ∈ Gamma N.natAbs`.
- **What**: If `N ∣ M`, then `T^M` is in `Γ(|N|)`.
- **How**: `rwa [Subgroup.T_zpow_mem_iff, Gamma_width, Int.natAbs_dvd]`.
- **Hypotheses**: `N ∣ M`.
- **Uses-from-project**: `Subgroup.T_zpow_mem_iff`, `Subgroup.Gamma_width`.
- **Used by**: Callers needing explicit membership of integer powers of `T`
  in a principal congruence subgroup.
- **Visibility**: public; namespace `Subgroup`.
- **Lines**: 68-69.

## File Summary
Seven public declarations (one `noncomputable def`, six `lemma`s) in
namespace `Subgroup`. Establishes the cusp-`∞` width `Subgroup.width` as
`relIndex Γ (zpowers T)`, the divisibility characterisation
`T^n ∈ Γ ↔ width ∣ n` (both nat and int variants), the basic fact
`width ≠ 0` for finite-index subgroups, and the identification
`Γ(N).width = N`. Self-contained — depends only on mathlib's modular
groups, cyclic group, and `Subgroup.relIndex` API; no project files
needed beyond mathlib. No `sorry`.
