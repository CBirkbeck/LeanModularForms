# Phase 3: Mathlib API Audit

Repo: `LeanModularForms/ForMathlib/` (~180 files, ~210 user-facing
declarations of `def`/`structure`/`class`/`abbrev`/`instance` kind).
This audit was produced by reading the per-file `*.md` inventories
under `/tmp/overview-inventory/` and cross-checking mathlib with
`lean_loogle` / `lean_leansearch` / `lean_leanfinder`.

Conventions used below:
- USE = mathlib has the exact concept; the project decl is redundant.
- GENERALIZE = mathlib has a strictly more general API the project decl
  is a specialisation of, so we should re-build on top.
- REPLACE = mathlib has a different but better-API form (different
  signature) that the project should switch to.
- KEEP = genuinely novel / paper-specific / no mathlib counterpart yet.

---

## A. Project definitions catalog

The full list is in `/tmp/overview-inventory/*.md` (≈ 210 entries).
Below is the high-impact subset, ranked by `Used by` reference count
across the whole project inventory (column `usage` = `wc -l` over
all `Uses-from-project` lines mentioning the symbol). All file paths
are relative to `/Users/mcu22seu/Documents/GitHub/LeanModularForms/`.

| # | declaration | file | what it represents | usage | mathlib status |
|---|---|---|---|---|---|
| 1 | `structure PwC1Immersion` | `LeanModularForms/ForMathlib/PiecewiseC1Path.lean` | piecewise-C¹ path with nonzero deriv + nonzero one-sided derivative limits | 104 | KEEP (mathlib has only `Path`, no piecewise-C¹ analog) |
| 2 | `structure ClosedPwC1Curve` / `ClosedPwC1Immersion` | `LeanModularForms/ForMathlib/PaperPwC1Immersion.lean` | paper-faithful (endpoints-in-partition) variants | 81 | KEEP, but consolidate (see B-1) |
| 3 | `def firstExitTimeLeft/Right` (+ `HW33ExitData`) | `LeanModularForms/ForMathlib/ExitTime.lean` | exit time `sInf {t ∈ Icc | ε ≤ ‖γ t − s‖}` | 54 | KEEP (paper-specific exit-time machinery) |
| 4 | `def cpvIntegrandOn` / `cauchyPrincipalValueIntegrandOn` | `LeanModularForms/ForMathlib/CauchyPrincipalValue.lean`, `Residue.lean` | ε-cutoff CPV integrand | 54 | KEEP (no mathlib equivalent) |
| 5 | `def tangentDeviation` / `def orthogonalProjectionComplex` | `LeanModularForms/ForMathlib/FlatnessConditions.lean` | ℝ-orthogonal projection onto a complex direction | 40+6 | GENERALIZE → `orthogonalProjection` / `Inner` API |
| 6 | `def generalizedWindingNumber'` / `def generalizedWindingNumber01` | `LeanModularForms/ForMathlib/ClassicalCPV.lean`, `WindingHomotopy.lean` | `(2πi)⁻¹ · PV ∫ dz/(z − z₀)` | 39 | KEEP (mathlib has only smooth-path winding via `curveIntegral`; PV variant is novel) |
| 7 | `def cauchyPV` / `cauchyPVOn` | `LeanModularForms/ForMathlib/CauchyPrincipalValue.lean` | `limUnder` of cutoff integrals | 36 | REPLACE: use `Tendsto`-only API (see B-2, C-1) |
| 8 | `def HasCauchyPV` / `HasCauchyPVOn` | same | `Tendsto … (𝓝[>] 0) (𝓝 L)` | 32 | KEEP (this is the good predicate) |
| 9 | `def principalPartSum` | `LeanModularForms/ForMathlib/PrincipalPart.lean` | `∑ s ∈ S, c s / (z − s)` | 28 | KEEP (concrete construction not in mathlib) |
| 10 | `def cauchyPrincipalValue'` (with `_` integrand) | `LeanModularForms/ForMathlib/ClassicalCPV.lean` | duplicate of (7) | 28 | REPLACE: see B-2 (delete primed pair, use (7)/(8) chain) |
| 11 | `structure PiecewiseC1Path` | `LeanModularForms/ForMathlib/PiecewiseC1Path.lean` | abstract piecewise-C¹ path on `[0,1]` | 26 | GENERALIZE → wrap mathlib's `Path` more tightly (already extends it); see C-2 |
| 12 | `structure ClosedImmersion` (+ `ContourCycle`) | `LeanModularForms/ForMathlib/Cycles.lean` | bundle of basepoint + closed `PwC1Immersion` | 17 | KEEP |
| 13 | `def angleAtCrossing` | `LeanModularForms/ForMathlib/GeneralizedResidueTheory/WindingNumber/Defs.lean` | crossing angle from one-sided derivative limits | 17 | KEEP |
| 14 | `def cpvIntegrand` (single-pole) | `LeanModularForms/ForMathlib/CauchyPrincipalValue.lean` | special case of (4) | 15 | REPLACE: delete; project already proves `cpvIntegrand = cpvIntegrandOn {z₀}` |
| 15 | `structure PiecewiseC1Curve` / `PiecewiseC1Immersion` | `LeanModularForms/ForMathlib/ClassicalCPV.lean` | open-interior-partition variant | 10+2 | REPLACE: delete primed `'` chain, keep the `PiecewiseC1Path` chain |
| 16 | `structure IsNullHomologous` | `LeanModularForms/ForMathlib/NullHomologous.lean` | image-in-U ∧ winding-zero-outside-U | 9 | KEEP (mathlib has no `IsNullHomologous` for generalised winding) |
| 17 | `def residueSimplePole` / `def HasSimplePoleAt` | `LeanModularForms/ForMathlib/Residue.lean` | residue = `lim (z − z₀)·f`, simple-pole decomposition | 8 / 8 | GENERALIZE → mathlib's `MeromorphicAt` + `meromorphicTrailingCoeffAt` (see B-3) |
| 18 | `def HW33ExitData` (+ `.ofExitTimes`) | `LeanModularForms/ForMathlib/ExitTime.lean` | exit-time bundle for HW Thm 3.3 | 7 | KEEP |
| 19 | `def poleOrderAt` | `LeanModularForms/ForMathlib/PrincipalPart.lean` | pole order ∈ ℕ | 6 | REPLACE: thin wrapper for `(-meromorphicOrderAt _ _).untop₀.toNat`. Could either be deleted or upstreamed (see B-3) |
| 20 | `structure SatisfiesConditionA'` / `SatisfiesConditionB` | `LeanModularForms/ForMathlib/FlatnessConditions.lean` | Hungerbuhler–Wasem conditions A', B | 5 | KEEP (paper definitions) |
| 21 | `structure IsFlatOfOrder` | `LeanModularForms/ForMathlib/FlatnessConditions.lean` | `‖tangDev‖ = o(‖γt - γt₀‖ⁿ)` on each side | 4 | GENERALIZE (cf. mathlib's `Asymptotics.IsLittleO` directly) |
| 22 | `def onCurvePVProvider` | `LeanModularForms/ForMathlib/ValenceFormula/PVChain/Helpers.lean` | predicate that PV exists at on-curve poles | 5 | KEEP (project-specific) |
| 23 | `def Finset.IsConsecutive` | `LeanModularForms/ForMathlib/PaperPwC1Immersion.lean` | `a, b ∈ s`, `a < b`, nothing strictly between | 10+ | REPLACE: use `Finset.Ioo a b ∩ s = ∅` directly, or upstream to mathlib (see C-3) |
| 24 | `def cyclicShiftFun` / `Path.cyclicShift` | `LeanModularForms/ForMathlib/PaperPwC1Immersion.lean` | cyclic shift of a closed path by `τ ∈ (0,1)` | ~10 | KEEP (specific, but should be upstreamed once cleaned) |
| 25 | `def windingNumberCycle` / `contourIntegralCycle` / `cpvCycle` | `Cycles.lean` | linear extension of winding / contour-integral / CPV to a cycle (a `ClosedImmersion →₀ ℤ`) | 3-4 each | KEEP |

The remaining ~180 declarations are either (i) FTC providers
(`arcFTCHyp_*`, `cornerFTCHyp_*`, `Seg1/Seg4/Arc/SectorCurve`),
(ii) project-specific geometric setup
(`fdBoundary_seg*_H`, `sArcOfS`, `sVertOfS`, `vertDelta`, `sectorCurve`),
(iii) modular-form bookkeeping (`oiFM`, `orbFM`, `ordOrbitQ`,
`ordOrbitFM`, `repCanon`, `s₀FM`, `repStrict`),
or (iv) one-off bundling structures
(`FDWindingData`, `ModularSideData`, `ResidueSideData`,
`PolarPartDecomposition`, `MultiCrossingScenario`,
`PerPoleCrossData`, `MultiPoleCrossScenario`, `LocalDerivedCutoffs`,
`CrossingGeometry`, `AsymmetricArcFTCHyp`,
`AsymmetricSingleCrossingData`, `PVChainData`, `WindingNumberHomotopyData`).
None of those has a mathlib analog – they are scaffolding for the
valence-formula proof and are KEEP at this stage.

---

## B. Definitions to REPLACE / GENERALIZE with mathlib

### B-1. The duplicate piecewise-C¹ chain

The project currently has **two** parallel chains of piecewise-C¹
structures and a third paper-faithful one:

* `PiecewiseC1Path x y` (`LeanModularForms/ForMathlib/PiecewiseC1Path.lean:52`) — extends mathlib's `Path x y`, with
  open-interior `partition`, `differentiable_off`, `deriv_continuous_off`.
* `PwC1Immersion x y` (`LeanModularForms/ForMathlib/PiecewiseC1Path.lean:?`) — extends the above with `deriv_ne_zero`
  + nonzero one-sided derivative limits.
* `PiecewiseC1Curve` / `PiecewiseC1Immersion` (`LeanModularForms/ForMathlib/ClassicalCPV.lean:30-56`)
  — second-generation copies on `[a,b]` (not `[0,1]`!) used **only**
  by `Residue.lean`, `WN-Defs.lean`, the `'`-suffixed `cauchyPrincipalValue'`,
  `generalizedWindingNumber'`, etc. They are essentially identical
  to (1) above but parameterised on `[a, b]` instead of `[0, 1]`.
* `ClosedPwC1Curve` / `ClosedPwC1Immersion` (`LeanModularForms/ForMathlib/PaperPwC1Immersion.lean:67-97`)
  — third copy with `partition ⊆ Icc 0 1` (endpoints in partition).

**Action**: collapse the `'`-suffixed chain (`PiecewiseC1Curve`,
`PiecewiseC1Immersion`, `cauchyPrincipalValue'`,
`cauchyPrincipalValueIntegrand'`, `generalizedWindingNumber'`) onto
the unprimed chain. A `PiecewiseC1Path 0 1` ≃ a `PiecewiseC1Curve`
with `a = 0`, `b = 1` after applying `Path.extend`. The `[a,b]`-version
is just `PiecewiseC1Path` precomposed with the affine map
`t ↦ a + (b-a) t`. **The whole `Residue.lean` (~750 lines) and
`ClassicalCPV.lean` (210 lines) can be re-routed through the unprimed
chain**, deleting both `PiecewiseC1Curve` and `PiecewiseC1Immersion`.

Impact: removes ~960 lines of duplicate API; gives ONE notion of
piecewise C¹ path.

### B-2. `cauchyPV` / `cauchyPVOn` / `cauchyPrincipalValue'` via `limUnder`

`CauchyPrincipalValue.lean:97-105` defines

```
def HasCauchyPV   (f γ z₀) (L : ℂ) : Prop := Tendsto … (𝓝[>] 0) (𝓝 L)
def cauchyPV     (f γ z₀)         : ℂ    := limUnder (𝓝[>] 0) …
```

and a multi-point pair (lines 200-208). The `_eq` bridge
`HasCauchyPV.cauchyPV_eq` is the only thing in the file that uses
`cauchyPV` non-trivially. Every downstream caller (per the
`Used by` graphs) ultimately wants `HasCauchyPV` /
`CauchyPrincipalValueExistsOn` and shows existence directly.
`cauchyPV` is the project memory's recommendation as "secondary".

**Action**: delete `cauchyPV`, `cauchyPVOn`, `cauchyPrincipalValue'`
(`ClassicalCPV.lean:76-78`). Keep only the `HasCauchyPV` /
`HasCauchyPVOn` / `CauchyPrincipalValueExists`/`On` predicates plus
the `Tendsto.unique` argument for value extraction.

This matches what mathlib does elsewhere (no `limUnder` versions are
shipped for, e.g., `iteratedDeriv`, `nhdsLimit`, etc.). It also kills
the only places in the project where `limUnder_eventually_eq_const`
(`Homotopy/Integrality.lean`, `WindingHomotopy.lean:70-75`) is needed.

### B-3. `residueSimplePole` + `HasSimplePoleAt` → `meromorphicTrailingCoeffAt`

`Residue.lean:63-70` defines

```
def residueSimplePole (f z₀) : ℂ := limUnder (𝓝[≠] z₀) (z ↦ (z - z₀) * f z)
def HasSimplePoleAt (f z₀)  : Prop := ∃ c g, AnalyticAt ℂ g z₀ ∧ … = c/(z - z₀) + g z
```

Mathlib has these:

* `MeromorphicAt f z₀` — `@[fun_prop]`, `Mathlib.Analysis.Meromorphic.Basic`.
* `meromorphicOrderAt f z₀ : WithTop ℤ` — `Mathlib.Analysis.Meromorphic.Order`.
* `meromorphicTrailingCoeffAt f z₀ : E` — `Mathlib.Analysis.Meromorphic.TrailingCoefficient`,
  defined exactly as the limit of `(z - z₀)^(-order) • f z` (matches
  the residue at order `-1`).
* `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt` — the
  `Tendsto` predicate that `residueSimplePole` is hand-rolling
  via `limUnder`.

The project already has a bridge (`MeromorphicBridge.lean:HasSimplePoleAt.residue_eq_coeff_of_order_neg_one`).
What is missing is to **canonicalise `residueSimplePole` as
`meromorphicTrailingCoeffAt` whenever the meromorphic order is `-1`**,
and to delete `poleOrderAt` (`PrincipalPart.lean:51-54`) in favour of
`(-meromorphicOrderAt f z).untop₀.toNat` (which is what the def
literally is, modulo a `MeromorphicAt` guard).

**Action**:

1. Replace every API call on `residueSimplePole f z₀` with
   `meromorphicTrailingCoeffAt f z₀` after upgrading the hypothesis
   to `MeromorphicAt f z₀` ∧ `meromorphicOrderAt f z₀ = -1`.
   The 5 places that use `residueSimplePole` are
   `Residue.lean:residue_simple_pole_eq_laurent`,
   `Residue.lean:integral_singular_term_eq_winding_times_coeff`,
   `Residue.lean:differentiableAt_singular_sum`,
   `Residue.lean:differentiableAt_g_off_poles`,
   `Residue.lean:continuousAt_g_at_pole`.
2. Delete `poleOrderAt`; keep the lemmas as direct consequences of
   `meromorphicOrderAt_eq_neg_one_of_hasSimplePoleAt` etc.
3. Keep `HasSimplePoleAt` as a thin alias if you want a paper-flavour
   predicate, but mark it deprecated in favour of
   `meromorphicOrderAt … = -1`.

### B-4. `tangentDeviation` / `orthogonalProjectionComplex` → mathlib's `orthogonalProjection`

`FlatnessConditions.lean:48-53` defines

```
def orthogonalProjectionComplex (w L : ℂ) : ℂ := (Re(w * conj L) / ‖L‖²) • L
def tangentDeviation              (w L : ℂ) : ℂ := w - orthogonalProjectionComplex w L
```

This is the ℝ-orthogonal projection of `w` onto `ℝ·L ⊂ ℂ`, hand-written.
Mathlib has `orthogonalProjection (𝕜 := ℝ) (K := Submodule.span ℝ {L})`
in `Mathlib.Analysis.InnerProductSpace.Projection` once you put a
real inner-product structure on ℂ (which it has via `Complex.instInnerProductSpaceReal`).

**Action**: rewrite the 8 declarations in `FlatnessConditions.lean:48-114`
using `orthogonalProjection (ℝ ∙ L) w`. The four basic lemmas
(`_zero_left`, `_zero_right`, `_real_smul_self`, `tangentDeviation_add`)
become free from mathlib, leaving only `norm_tangentDeviation_le`
(which is the easy estimate `‖x - proj K x‖ ≤ ‖x‖ + ‖proj K x‖ ≤ 2‖x‖`).

Impact: shrinks `FlatnessConditions.lean:48-114` from ~70 lines to
~10 lines and unlocks `orthogonalProjection.norm_le_norm`,
`orthogonalProjection_smul_self` etc.

### B-5. `IsFlatOfOrder` → use raw `Asymptotics.IsLittleO`

`FlatnessConditions.lean:128-136` packages two `IsLittleO` statements
into a structure. Two of the three subsequent lemmas
(`IsFlatOfOrder.of_le`, `isFlatOfOrder_zero`, `isFlatOfOrder_one`)
are direct `IsLittleO.trans_isBigO` arguments that don't need the
wrapper. The structure adds nothing semantically.

**Action**: drop the structure; switch to a definitional `Prop`
alias

```
def IsFlatOfOrder (γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop :=
  (∀ L, …  =o[𝓝[<] t₀] (· -- power)) ∧ (… right side)
```

or even drop the alias entirely. The savings are modest (the
`mk_iff`-style API is unused), but it lets `fun_prop` see through it.

---

## C. API-poor choices that should be API-rich

### C-1. `limUnder` instead of `Tendsto`

The project uses `limUnder` to give a "value" to a Cauchy principal
value or residue when the limit may not exist. This shows up in
**five** independent files:

* `LeanModularForms/ForMathlib/CauchyPrincipalValue.lean:103-105` — `cauchyPV`,
  `cauchyPVOn`.
* `LeanModularForms/ForMathlib/ClassicalCPV.lean:76-78` — `cauchyPrincipalValue'`.
* `LeanModularForms/ForMathlib/Residue.lean:45-50, 63-64` — `cauchyPrincipalValueOn`,
  `residueSimplePole`.
* `LeanModularForms/ForMathlib/WindingHomotopy.lean:64-66` — `generalizedWindingNumber01`.
* `LeanModularForms/ForMathlib/GeneralizedResidueTheory/Homotopy/Integrality.lean:limUnder_eventually_eq_const`
  — utility lemma to push `limUnder` past eventually-constant
  predicates.

The downstream lemmas immediately fight to get back to `Tendsto`
(every `…_eq` lemma is `Tendsto.limUnder_eq` and every consumer
turns it back around). The `limUnder` form is junk-on-no-limit, and
nothing in the codebase exploits the junk.

**Action**:

1. Delete `cauchyPV`, `cauchyPVOn`, `cauchyPrincipalValue'`,
   `cauchyPrincipalValueOn`, `residueSimplePole`,
   `generalizedWindingNumber01` (the *values*). Keep only the
   `Has…` predicates (Tendsto-formulated) and `…Exists` definitions.
2. Where a "value" is genuinely wanted (e.g. for the assembled
   contour-integral sum), thread `Classical.choose` of the existence
   proof, or push the existence into the hypothesis (most theorems
   already need existence).
3. Delete `limUnder_eventually_eq_const`.

The pattern matches mathlib: `iteratedDeriv` exists as a value
because it's always well-defined; `Tendsto` is the predicate of
choice for "limits that may fail". This project conflates the two.

### C-2. `PiecewiseC1Path` lacks `fun_prop` decoration

The single most-used structure in the codebase (104 references) has
**no** `@[fun_prop]` decoration anywhere. Mathlib's `MeromorphicAt`,
`AnalyticAt`, `Continuous`, `Differentiable*` all carry `@[fun_prop]`,
but the project's `PwC1Immersion.toFun` / `extend` /
`PwC1Immersion.continuous` / `PwC1Immersion.differentiable_off` / etc.
do not. As a result, every continuity / differentiability proof
involving `γ.toFun` or `γ.toPath.extend` is hand-written.

**Action**: add `@[fun_prop]` to the following theorems
(all in `LeanModularForms/ForMathlib/PiecewiseC1Path.lean`,
`LeanModularForms/ForMathlib/PaperPwC1Immersion.lean`):

* `PiecewiseC1Path.continuous`, `PiecewiseC1Path.continuous_extend`,
  `apply_zero`, `apply_one`.
* `ClosedPwC1Curve.continuous`,
  `ClosedPwC1Curve.lipschitzWith_extend`,
  `ClosedPwC1Curve.deriv_extend_intervalIntegrable`.
* `ClosedPwC1Immersion.lipschitzWith_extend`.
* `PwC1Immersion.differentiable_off`, `PwC1Immersion.deriv_ne_zero`.

For the corresponding existential one-sided derivative limits
(`PwC1Immersion.left_deriv_limit`, `right_deriv_limit`), bundle
them as `HasDerivWithinAt … (Iio t)` / `(Ioi t)` rewrites with
`Filter.Tendsto.hasDerivWithinAt`.

Impact: ~80 hand-written `(.add continuousOn_const).norm`,
`(γ.toPath.continuous_extend.comp …)` chains in the file inventories
become single `fun_prop` calls.

### C-3. `Finset.IsConsecutive` could go to mathlib

`PaperPwC1Immersion.lean:62-65`:

```
def Finset.IsConsecutive (s : Finset ℝ) (a b : ℝ) : Prop :=
  a ∈ s ∧ b ∈ s ∧ a < b ∧ ∀ c ∈ s, ¬(a < c ∧ c < b)
```

Used by 10+ project lemmas; mathlib does not have this concept.
The predicate is dual to `Finset.Ioo a b ∩ s = ∅`.

**Action**: upstream `Finset.IsConsecutive` and the basic API
(`exists_consecutive_pair_containing`, `cyclic_lift`, etc.) once the
proof is polished. Or, **before** upstreaming, rewrite as

```
def Finset.IsConsecutive [LinearOrder α] (s : Finset α) (a b : α) :=
  a ∈ s ∧ b ∈ s ∧ a < b ∧ Finset.Ioo a b ∩ s = ∅
```

so the API picks up `Finset.mem_Ioo`, `Finset.inter_empty_iff`, etc.
The current implementation as a 4-conjunct `Prop` is hand-rolled
membership/order reasoning.

### C-4. `firstExitTimeLeft/Right` could split into 2 helpers + `sInf` API

`ExitTime.lean` defines `firstExitTimeRight` (`sInf`) and
`firstExitTimeLeft` (`sSup`), then proves 22 lemmas about them in a
hand-rolled `csInf`/`csSup` style. The closed-radius-attainment
(`norm_at_firstExitTimeRight_eq`, 32 lines) is the canonical
"continuous-function-attains-its-boundary-value-on-a-closed-set"
argument that mathlib expresses via `IsClosed.csInf_mem`.

The existing proofs are correct, but spread thinly. The headline lemma
`HW33ExitData.ofExitTimes` packages 6 different exit-time facts into
one structure — that's the only consumer, so the entire structure
could be one fewer indirection (i.e. inline the 4 fields at the
single call site).

**Action**: keep `firstExitTimeLeft/Right` (they are the natural
witnesses), but redo the proofs using
`ContinuousOn.csInf_mem_of_isClosed_of_nonempty_bdd` /
`Set.OrdConnected` API in one stroke per side, cutting the file
from 320 lines to ~150.

### C-5. `IsNullHomologous.winding_eventually_zero_cocompact_of_bounded` uses `Bornology.IsBounded`

`NullHomologous.lean:173-184` already uses `Bornology.IsBounded` and
`Filter.cocompact`. This is the right API. But the same file
hand-rolls `lipschitzWith_norm_bound_on_Icc01` (`190-212`, 23 lines)
to bound a Lipschitz path's norm on `[0,1]`. Mathlib has
`LipschitzWith.dist_le_mul` + `dist_le_norm_add_norm` combining to a
single `nlinarith` step.

**Action**: replace `lipschitzWith_norm_bound_on_Icc01` with an
inline 3-line proof; or delete the helper entirely and inline at
its two callers
(`generalizedWindingNumber_eq_zero_of_far_lipschitz`,
`winding_eventually_zero_cocompact_of_lipschitz`).

---

## D. Hand-rolled patterns to refactor

### D-1. ε-δ proofs that should be `Tendsto.eventually_*`

* `ExitTime.lean:143-164`, `267-288` — `t₀_lt_firstExitTimeRight`,
  `firstExitTimeLeft_lt_t₀`. The proofs extract an `η` from
  `Metric.nhdsWithin_basis_ball` and derive a contradiction via
  `not_le.mpr`. Mathlib has `Tendsto.eventually_lt_const` already
  used here, but the surrounding scaffolding (computing `min η δ / 2`,
  destructuring the basis) is 15 lines that could be one
  `filter_upwards [hη_event] with t ht; exact …`.
* `ExitTime.lean:171-202` (`norm_at_firstExitTimeRight_eq`,
  32 lines), `293-324` (`norm_at_firstExitTimeLeft_eq`, 32 lines)
  — both reduce to `IsClosed.csInf_mem` / `IsClosed.csSup_mem` plus
  the standard "strictly-greater-than-boundary contradicts inf"
  pattern. This is exactly what mathlib's
  `ContinuousOn.csInf_mem` and `Set.IsClosed.csInf_mem` already do.
* `Residue.lean:609-638` (`cpv_eq_classical_eventually_of_avoids`,
  >10 lines) — image-compact + `infDist`-pos + δ-choice argument.
  Mathlib has `IsCompact.exists_ball_subset_compl_of_disjoint` or
  the cleaner `Metric.infDist_pos_iff_notMem_closure`-based path.

### D-2. Manual `IntervalIntegrable` from piecewise continuity

* `ClassicalCPV.lean:109-122, 125-139` — two private lemmas
  `aestronglyMeasurable_of_continuousOn_off_finite` and
  `intervalIntegrable_of_piecewise_continuousOn_bounded`. Mathlib has
  `ContinuousOn.intervalIntegrable_of_Icc` plus
  `aestronglyMeasurable_indicator_of_measurableSet` /
  `MeasureTheory.AEStronglyMeasurable.union`; together they give
  the same result in 4 lines.
* `Residue.lean:205-221` — `piecewiseC1_deriv_intervalIntegrable` —
  same: `ContinuousOn.intervalIntegrable` + the (finite) partition
  reasoning is hand-rolled.
* `PaperPwC1Immersion.lean:157-222` —
  `intervalIntegrable_of_consecutive_pieces` (66 lines!), and the
  identical structure 358-573 for `LipschitzOnWith`. Both are
  strong-induction-on-Finset arguments. **Action**: extract one
  reusable `Finset.strongInductionOn`-with-consecutive-pair API and
  upstream alongside `Finset.IsConsecutive`.

### D-3. Hand-rolled compact-image / discrete arguments

* `PaperPwC1Immersion.lean:1605-1659` —
  `preimage_finite_piece` (54 lines), proving a piecewise C¹
  immersion has finitely many preimages of any point on a closed
  piece. This is "closed + discrete-topology + compact ⇒ finite",
  built from `HasDerivWithinAt.eventually_ne`,
  `discreteTopology_of_noAccPts`, `accPt_principal_iff_nhdsWithin`,
  `isCompact_iff_compactSpace`, `finite_of_compact_of_discrete`,
  `Set.finite_coe_iff`. Mathlib's
  `Set.Finite.subset_of_isCompact_of_isClosed_of_discreteTopology`
  encapsulates this in one lemma.

### D-4. Tendsto.congr' / Tendsto.congr boilerplate

There are ~20 instances across `CauchyPrincipalValue.lean`,
`Residue.lean`, `WindingHomotopy.lean`, `Homotopy/Invariance.lean`,
`FDBoundaryReparametrization.md` where the pattern is

```
have heq : f =ᶠ[l] g := by …
exact (hg.congr' heq.symm)  -- or similar
```

These are unavoidable, but several can be collapsed into single
`filter_upwards [hg, heq] with x hxg hxeq …` blocks.

### D-5. Sum-of-`Finsupp` decompositions

* `Cycles.lean:154-170` (`sum_swap_winding_residue`, 17 lines) — a
  `Finset.mul_sum` + `Finset.sum_comm` argument that is canonical.
  Once `windingNumberCycle` is exposed via `Finsupp.sum`, this becomes
  `Finsupp.sum_comm`.
* `Cycles.lean:198-214` (`windingNumberCycle_isInt`, 17 lines) — a
  `Finset.sum_induction` over "is integer" closed under `+, *, 0`.
  Mathlib has `Finset.sum_intCast` and `Subsemiring.copy` helpers,
  but the explicit induction is fine.

### D-6. Custom `_eventuallyEq` rewrites in `NullHomologous`

* `NullHomologous.lean:219-256` (`contourIntegral_inv_norm_le_of_far`,
  38 lines) — pointwise norm bound + `inv_anti₀` + `norm_integral_le_of_norm_le_const`.
  The 38-line proof is doing exactly what `intervalIntegral.norm_integral_le_of_norm_le_const`
  does; the rest is reverse-triangle and `inv_le_div`. Can compress to ~12 lines.

---

## E. Missing automation hooks

| Decl | File:line | Suggested tag | Why |
|---|---|---|---|
| `PiecewiseC1Path.apply_zero` / `apply_one` | `LeanModularForms/ForMathlib/PiecewiseC1Path.lean:77, 81` | already `@[simp]` | OK |
| `PiecewiseC1Path.continuous` | `LeanModularForms/ForMathlib/PiecewiseC1Path.lean:88` | `@[fun_prop]` | top fun_prop hook for the project |
| `PiecewiseC1Path.extendedPath_eq` | `LeanModularForms/ForMathlib/PiecewiseC1Path.lean:73` | already `@[simp]` | OK |
| `ClosedImmersion.toPath_eq` | `LeanModularForms/ForMathlib/Cycles.lean:66` | already `@[simp]` | OK |
| `ClosedImmersion.coe_eq` | `LeanModularForms/ForMathlib/Cycles.lean:74` | already `@[simp]` | OK |
| `contourIntegral_zero` | `LeanModularForms/ForMathlib/PiecewiseContourIntegral.lean:87` | `@[simp]` | natural simp rule |
| `contourIntegral_neg` | `same:67` | `@[simp]` | natural simp rule |
| `contourIntegralCycle_zero` | `LeanModularForms/ForMathlib/Cycles.lean:264` | `@[simp]` | needed for `Finsupp.sum` |
| `windingNumberCycle_zero` | `Cycles.lean:269` | `@[simp]` | needed for `Finsupp.sum` |
| `cpvCycle_zero` | `Cycles.lean:280` | `@[simp]` | needed for `Finsupp.sum` |
| `cyclicShiftFun_zero`/`_one` | `LeanModularForms/ForMathlib/PaperPwC1Immersion.lean:744-762` | already `@[simp]` (one branch) | OK |
| `PwC1Immersion.differentiable_off` | structure projection, `LeanModularForms/ForMathlib/PiecewiseC1Path.lean:?` | `@[fun_prop]` | composition pre-condition |
| `principalPartSum_differentiableOn` / `_analyticAt` / `_meromorphicAt` | `LeanModularForms/ForMathlib/PrincipalPart.lean:117-285` | `@[fun_prop]` | composition with `principalPartSum` is everywhere |
| `differentiableAt_div_sub` | `LeanModularForms/ForMathlib/PrincipalPart.lean:106-109` | `@[fun_prop]` | one-pole `1/(z-s)` is a fundamental brick |
| `HasSimplePoleAt.meromorphicAt` | `LeanModularForms/ForMathlib/MeromorphicBridge.lean:?` | `@[fun_prop]` | bridge to `MeromorphicAt` |
| `IsNullHomologous` fields | `LeanModularForms/ForMathlib/NullHomologous.lean:57-62` | `@[mk_iff]` | so `IsNullHomologous.mk ↔ ⟨image_subset, winding_zero⟩` becomes auto |
| `IsFlatOfOrder` (structure) | `LeanModularForms/ForMathlib/FlatnessConditions.lean:128-136` | `@[mk_iff]` | currently nothing |
| `PiecewiseC1Path` / `PwC1Immersion` / `ClosedPwC1Curve` / `ClosedPwC1Immersion` | structures | `@[ext]` | structural extensionality not exposed |
| `cpvIntegrand_of_gt` / `cpvIntegrand_of_le` | `LeanModularForms/ForMathlib/CauchyPrincipalValue.lean:71-81` | already `@[simp]` | OK |
| `cpvIntegrandOn_of_forall_gt` / `_of_exists_le` | `same:169-182` | already `@[simp]` | OK |

Total: **~14 new `@[fun_prop]` candidates**, **~5 `@[simp]` candidates**,
**~4 `@[ext]` candidates**, **~2 `@[mk_iff]` candidates**.

---

## F. Headline action items (top 10)

Numbered roughly by impact = (lines saved) × (downstream API gained).

1. **Delete duplicate `PiecewiseC1Curve`/`PiecewiseC1Immersion` chain**
   (`LeanModularForms/ForMathlib/ClassicalCPV.lean:30-56`, plus the `'`-suffixed
   `cauchyPrincipalValue'`, `cauchyPrincipalValueIntegrand'`,
   `generalizedWindingNumber'`); route `Residue.lean` (~750 lines) and
   `WN-Defs.lean` through the unprimed `PiecewiseC1Path` / `PwC1Immersion`.
   **Impact**: removes ~960 lines of duplicate API; one notion of
   piecewise-C¹ path. (B-1)

2. **Replace `residueSimplePole` with `meromorphicTrailingCoeffAt`**
   (`LeanModularForms/ForMathlib/Residue.lean:63-64`).
   Delete `poleOrderAt` (`PrincipalPart.lean:51-54`). Keep `HasSimplePoleAt`
   as deprecated alias for `meromorphicOrderAt … = -1`.
   **Impact**: ~50 lines saved, full mathlib `MeromorphicAt`/`AnalyticAt`
   API unlocks (in particular `meromorphicTrailingCoeffAt_neg`,
   `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt`,
   isolated-zeros, etc.). (B-3)

3. **Delete `cauchyPV` / `cauchyPVOn` / `cauchyPrincipalValue'` /
   `generalizedWindingNumber01`** (the `limUnder`-flavoured values)
   in `LeanModularForms/ForMathlib/CauchyPrincipalValue.lean:103-208`,
   `ClassicalCPV.lean:76-78`, `Residue.lean:45-50`,
   `WindingHomotopy.lean:64-66`. Keep only `Has…` predicates +
   `…Exists`. Delete the `limUnder_eventually_eq_const` helper.
   **Impact**: ~100 lines of definitions + ~30 lines of bridging lemmas
   removed; the project becomes consistent with mathlib's
   "Tendsto-as-predicate" convention. (C-1)

4. **Add `@[fun_prop]` to the geometric API**
   (`PiecewiseC1Path.lean`, `PaperPwC1Immersion.lean`, `Cycles.lean`,
   `PrincipalPart.lean`, `MeromorphicBridge.lean`). At minimum the
   14 declarations listed in §E.
   **Impact**: every continuity/differentiability proof involving
   `γ.toFun`/`γ.toPath.extend` reduces to `fun_prop`.
   Concrete: the `~80` hand-written `.add continuousOn_const` /
   `(γ.toPath.continuous_extend.comp …)` chains collapse. (C-2)

5. **Refactor `FlatnessConditions.lean:48-114`** to use mathlib's
   `orthogonalProjection` over `Submodule.span ℝ {L}` instead of
   the hand-defined `orthogonalProjectionComplex`/`tangentDeviation`.
   **Impact**: ~60 lines saved; unlocks
   `orthogonalProjection.norm_le_norm`, `orthogonalProjection_smul_self`. (B-4)

6. **Compress `PaperPwC1Immersion.lean`'s `intervalIntegrable_of_consecutive_pieces`
   (66 lines) and `lipschitzOnWith_of_consecutive_pieces` (55 lines)**
   to a single shared `Finset.strongInductionOn`-with-consecutive-pair
   utility, then upstream `Finset.IsConsecutive` (rewritten via
   `Finset.Ioo a b ∩ s = ∅`).
   **Impact**: ~80 lines saved; unblocks upstreaming. (D-2, C-3)

7. **Replace `preimage_finite_piece`** (`PaperPwC1Immersion.lean:1605-1659`,
   54 lines) with the canonical
   "closed-discrete-on-compact ⇒ finite" template via
   `Set.Finite.subset_of_isCompact_of_isClosed_of_discreteTopology`.
   **Impact**: ~40 lines saved. (D-3)

8. **Tag with `@[simp]`/`@[ext]`/`@[mk_iff]`** the 11 candidates in §E:
   - `contourIntegral_zero`, `contourIntegral_neg` (`@[simp]`).
   - `contourIntegralCycle_zero`, `windingNumberCycle_zero`,
     `cpvCycle_zero` (`@[simp]`).
   - `IsNullHomologous`, `IsFlatOfOrder` (`@[mk_iff]`).
   - `PiecewiseC1Path`, `PwC1Immersion`, `ClosedPwC1Curve`,
     `ClosedPwC1Immersion` (`@[ext]`).
   **Impact**: removes the manual `mk` calls + manual `ext`
   destructurings sprinkled across `Cycles.lean`, `NullHomologous.lean`,
   `FlatnessConditions.lean`.

9. **Use mathlib's `curveIntegral`** (`Mathlib.MeasureTheory.Integral.CurveIntegral.Basic`)
   as the eventual target for `PiecewiseContourIntegral.contourIntegral`.
   `curveIntegral` works on `Path a b` with `ω : E → E →L[𝕜] F`,
   which is the more general (and homotopy-invariant) formulation.
   The project's `contourIntegral f γ = ∫ t in 0..1, f(γ t) · γ' t`
   is the special case `ω z := f z • (· : ℂ →L[ℂ] ℂ)`. Mathlib's
   `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`
   (Poincaré) plus `curveIntegral_trans` / `curveIntegral_symm` / `curveIntegral_refl`
   give a richer API than the project's
   `contourIntegral_eq_sub_of_hasDerivAt`. **Impact**: long-term, the
   entire `PiecewiseContourIntegral.lean` (329 lines) becomes a thin
   bridge into mathlib `curveIntegral`. Short term, **at least**
   annotate the project def as definitionally equal so users can
   simp-rewrite into it.

10. **Compress `ExitTime.lean`** (320 lines, 22 lemmas) using
    `IsClosed.csInf_mem` / `IsClosed.csSup_mem` consistently.
    Inline `HW33ExitData.ofExitTimes` at its single consumer
    `HW33ExitData`. **Impact**: ~150 lines saved without losing API.
    (C-4)

---

### Final notes / cross-cutting findings

* The biggest single saving is **collapsing the two parallel
  piecewise-C¹ chains**. Almost all the "API duplication" in the
  audit ultimately comes from `PiecewiseC1Curve`/`PiecewiseC1Immersion`
  living alongside `PiecewiseC1Path`/`PwC1Immersion`.
* The `limUnder`-vs-`Tendsto` issue is the second biggest source of
  hand-rolled boilerplate. The project's memory document even flags
  this ("`HasCauchyPV` predicate is the primary API; `cauchyPV`
  is secondary"), but the secondary forms are never deleted.
* Mathlib's `MeromorphicAt` ecosystem (`meromorphicOrderAt`,
  `meromorphicTrailingCoeffAt`, `MeromorphicNFAt`) covers the
  residue / pole-order infrastructure substantially; the project's
  `residueSimplePole`/`poleOrderAt`/`HasSimplePoleAt` are partially
  redundant.
* Mathlib has `curveIntegral` since ~Q1 2026; the project pre-dates
  it. This is the single biggest API to migrate towards once the
  unprimed `PiecewiseC1Path` becomes the canonical chain.
* No `@[fun_prop]` tag exists anywhere in `LeanModularForms/ForMathlib/`,
  despite mathlib having a robust `fun_prop` ecosystem. Adding the
  ~14 hooks in §E would be the most user-visible improvement.
