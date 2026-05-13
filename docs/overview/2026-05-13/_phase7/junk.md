# Phase 7: Junk / Removable

## A. Files with NO IMPORTERS — actually dead?

The reverse-imports map shows that *every* file in `ForMathlib/` is "NO IMPORTERS" because the reverse map only looks at intra-`ForMathlib/` imports. To find files truly orphaned, I computed:

```
all ForMathlib modules: 183
modules imported by SOME .lean file in the project: 168
truly orphaned (nothing imports them anywhere): 15
```

Genuinely orphan files (not imported by anything, including outside ForMathlib):

| File | Status | Recommendation |
|------|--------|----------------|
| `AtImInfty.lean` | live shim (Mathlib lemmas, 17 lines) | KEEP — extension of `atImInfty` API, simple; consider PR to mathlib |
| `Bounds.lean` | DEAD (340 lines, entire body in `/- ... -/` block comment) | **DELETE** — body inert; if anything wanted, recover content from git history |
| `CongruenceSubgroupsCopy.lean` | placeholder stub (15 lines, just a docstring) | **DELETE** — explicitly says "retained as empty placeholder"; no imports rely on it |
| `Cycles.lean` | real (ContourCycle definitions) | review — root file with API but no callers; **likely DELETE or repurpose** |
| `FunctionsBoundedAtInfty.lean` | live shim (9 lines: `IsBoundedAtImInfty.neg` alias) | KEEP — small shim ready for PR to mathlib |
| `hassumunifon.lean` | **DEAD** (1023 lines, entire body in `/- ... -/` block comment) | **DELETE** — see Section F |
| `HorizontalContribution.lean` | real (seg5/horizontal contribution proof) | Orphan — not imported anywhere. **DELETE or wire into ValenceFormula chain** |
| `HW33Clean.lean` | **HEADLINE/root** file (487 lines, paper-faithful HW 3.3 API) | KEEP — root theorem, the unified HW 3.3 entrypoint |
| `IsBoundedAtImInfty.lean` | DEAD (78 lines, entire body in `/- ... -/` block comment) | **DELETE** — body inert |
| `LevelOne.lean` | DEAD (55 lines, entire body in `/- ... -/` block comment) | **DELETE** — body inert |
| `ResidueSideProof.lean` | real (residue side of PV chain) | Orphan — old chain artifact; **DELETE if ValenceFormulaBridged covers it** |
| `SlashActions.lean` | live shim (44 lines, `ModularForm.slash_neg_one` family) | KEEP — extension lemmas, PR-ready candidate |
| `UpperHalfPlane.lean` | live shim (12 lines, `ModularGroup.modular_S_sq`) | KEEP — small, PR-ready |
| `ValenceFormulaFinal.lean` | **HEADLINE/root** file (70 lines, the final unconditional valence formula) | KEEP — root theorem |
| `WindingHomotopy.lean` | real (winding-number homotopy invariance) | Orphan — not imported anywhere; the GRT.Homotopy chain superseded it. **DELETE** |

## B. Dead declarations (private + unused in file)

| Declaration | File | Lines | Status |
|-------------|------|-------|--------|
| `fdBoundary_sub_I_at_35_im_neg` | ArcFTCAtI.lean | — | dead (private + unused) |
| `instance : NormSMulClass ℝ ℂ` (×3 instances) | Boundary-Smooth.lean | — | local instances, never used in file |
| `unit_circle_re_neg_half_eq_rho` / `_pos_half_eq_rho_plus_one` | CoreIdentityProof.lean | — | dead micro-lemmas |
| `volume_ball_preimage_tendsto_zero` | Crossing.lean | — | unused theorem |
| `norm_sub_pos_on_farSet` | GammaAnalysis.lean | — | dead private lemma |
| `pv_piecewise_measurable`, `pv_piecewise_bound`, `pv_piecewise_pointwise` | GRT-PrincipalValue.lean | — | three dead private theorems |
| `pv_simple_pole_integrand_split`, `pv_simple_pole_tendsto` | GRT-PrincipalValue.lean | — | two more dead private theorems |
| `laurentHigherOrderPolarAt_eventuallyEq_analytic_of_crossed` | HW33LaurentPolarPart.lean | — | dead private theorem |
| `two_pi_I_ne_zero_ms` | ModularSideProof.lean | — | dead local micro-lemma |
| `ge_one_sub_tau_of_second_clause`, `le_one_sub_tau_of_first_clause` | PaperPwC1Immersion.lean | — | dead private theorems |
| `pvIntegral_vertical_cancel` | PVChain-Assembly.lean | — | dead private theorem |
| `modularFormCompOfComplex_periodic` | PVChain-Helpers.lean | — | dead private theorem |
| `instance _ : IsScalarTower ℝ ℂ ℂ` | PVChain-ResidueSideInfra.lean | — | duplicate of `Instances.lean` instance |
| `A_int_eq_greg_mul_deriv` | Residue-MultipointPV-DominatedConvergence.lean | — | dead private lemma |
| `ref_seg4_I_neg_slitPlane` | SegmentAnalysis.lean | — | dead private lemma |
| `limUnder_eventually_eq_const` | WindingHomotopy.lean | — | dead (file itself orphan; see Section A) |
| `cutoff_integral_eq_ftc` | WindingWeights-Rho.lean | — | dead private lemma |

Total: ~24 dead private declarations across ~16 files. Each is a mechanical removal.

## C. Mathlib duplicates (proven trivially, mathlib has it)

Identified candidates (from inventory `**How**` short proofs):

- `instNormSMulClassRealComplex`, `instIsBoundedSMulRealComplex`, `instContinuousSMulRealComplex` in `Instances.lean` — these are workarounds for Mathlib 4.29 instance-loop changes; once Mathlib stabilizes, these become identity-typeclass shims. Likely to migrate upstream.
- `IsBoundedAtImInfty.neg` in `FunctionsBoundedAtInfty.lean` — straightforward 2-line alias; PR-ready for mathlib.
- `Subgroup.Gamma_width`, `Subgroup.T_zpow_mem_iff`, `Subgroup.T_pow_mem_iff` etc. in `CongruenceSubgrps.lean` — congruence-subgroup width API, all PR-worthy upstream.
- `ModularForm.slash_neg_one`, `slash_neg_one'`, `slash_neg`, `slash_neg'` in `SlashActions.lean` — PR candidates.
- `ModularGroup.modular_S_sq : S * S = -1` in `UpperHalfPlane.lean` — single-line theorem (file is one line of real content); already at the "right" place per file comment.
- `Filter.eventually_atImInfty`, `Filter.tendsto_im_atImInfty` in `AtImInfty.lean` — PR-ready.

These are not "duplicates" but explicit "for-mathlib" extension files — most ARE the kind of content this directory is meant to hold, and many should be PR'd upstream rather than deleted.

## D. Wrapper functions (1-2 mathlib calls — should inline)

Sample wrappers identified via `**How**: by exact ...` or single-line proofs:

- `hasCauchyPV_simple_pole_zero` in `Residue.lean` (lines 92–95): just `simpa using hasCauchyPV_simple_pole (c := 0) hw`. Inline.
- `hasSimplePoleAt_of_decomposition` in `Residue.lean` (lines 64–67): trivially `⟨c, g, hg, hf⟩`. Inline at call sites.
- Numerous "Used by: unused in file" privates in CoreIdentityProof.lean (e.g. `unit_circle_re_*_eq_*`) — single-shot rewrites that would be one-line `convert` at the call site.
- `cpvIntegrandOn_singleton_eq_*` (HW33Bridge.lean, lines 56–70): three lemmas, each a one-line invocation of `cpvIntegrandOn_of_*`. Can be combined or inlined.
- `ellipticPointI'_coe`, `ellipticPointI'_im` (ValenceFormula.lean, lines 44–45): `rfl` and `Complex.I_im`. Inline.

Likely 30-50 such wrappers across all inventory files; the high-value ones are the CoreIdentityProof and HW33Bridge clusters.

## E. Tiny façade / shim files to evaluate

| File | Lines | Purpose | Recommendation |
|------|-------|---------|----------------|
| `UpperHalfPlane.lean` | 12 | `ModularGroup.modular_S_sq` only | KEEP (PR-ready) |
| `FunctionsBoundedAtInfty.lean` | 9 | `IsBoundedAtImInfty.neg` alias | KEEP (PR-ready) |
| `AtImInfty.lean` | 17 | `eventually_atImInfty` + `tendsto_im_atImInfty` | KEEP (PR-ready) |
| `Instances.lean` | 31 | 4 typeclass instance workarounds | KEEP (Mathlib 4.29 patch); ideally upstream when instance loops fixed |
| `TrigLemmas.lean` | 30 | 3 trig identities (cos/sin 2π/3 + `exp_real_angle_I`) | KEEP (PR-ready); `cos_two_pi_div_three` etc may already be in mathlib |
| `Identities.lean` | 40 | **DEAD** (entire body in `/- ... -/`) | **DELETE** |
| `CongruenceSubgroupsCopy.lean` | 15 | explicit placeholder stub | **DELETE** — its docstring literally says it's retained as an empty placeholder |
| `CongruenceSubgrps.lean` | 71 | Real content (width API for SL₂(ℤ) subgroups) | KEEP (PR-ready); ideally upstream as it's `for_mathlib` material |
| `SlashActions.lean` | 44 | `slash_neg*` family | KEEP (PR-ready) |
| `LevelOne.lean` | 55 | **DEAD** (entire body in `/- ... -/`) | **DELETE** |

## F. The hassumunifon situation

**Confirmed**: `LeanModularForms/ForMathlib/hassumunifon.lean` is 1023 lines and its **entire body is wrapped in a block comment**.

- Line 1: `/- /-` — opens an outer block comment AND a nested inner one
- Lines 1-5: inner block ends with `-/` at line 5
- Lines 6-1022: actual Lean code (imports, `#min_imports`, theorems, the `my_sum_simp` elab, ~50 lemmas)
- Line 1023: ` -/` — closes the outer block comment that started at line 1

The Lean parser will treat the entire file body as a single comment, producing zero declarations. The inventory metadata (`hassumunifon.md` lines 1–1023 listing many "unused in file" theorems) is technically misleading since none of these declarations actually exist in the compiled file.

**Recommendation**: One of:
1. **DELETE the file** (preferred, since nothing imports it).
2. **De-comment + integrate** — if the lemmas about `HasSumUniformlyOn`/`SummableLocallyUniformlyOn`/`derivWithin_tsum` are genuinely needed for upstream PRs, fix the comment wrapping (delete the leading `/- ` on line 1 and the trailing ` -/` on line 1023), then either prune the inert duplicates against mathlib or PR them upstream.

Other "entire-body-commented" files (same `/- /-` ... `-/` pattern) — identified in this audit:

- `IsBoundedAtImInfty.lean` (78 lines, EisensteinSeries bounded-at-infty material)
- `LevelOne.lean` (55 lines, level-one cuspFunction analysis)
- `Identities.lean` (40 lines, T-width slash-invariance)
- `Bounds.lean` (340 lines, ModularFormClass/CuspFormClass exists_bound)
- `Petersson.lean` (verified by tail: ends with ` -/` — entire body in block comment)
- `QExpansion.lean` (verified by tail: ends with ` -/` — entire body in block comment)

That is **7 files** totaling roughly **1600+ lines of inert code masquerading as source**.

## G. Façade-file proliferation analysis

### HW33 chain

The directory contains 21 files with `HW33` prefix:

```
HW33Bridge.lean         305 lines   used by HW33Final
HW33Clean.lean          487 lines   ORPHAN — the live, headline file
HW33Closed.lean         133 lines   used by HW33Tight
HW33ExitTimeWrapper.lean              used by HW33Bridge
HW33Final.lean          247 lines   used by HW33MultiPole, HW33SectorEven
HW33HigherOrderAuto.lean              used by HW33LaurentSimple, HW33PVSing
HW33HigherOrderAvoidance.lean         used by HW33HoloCancel
HW33HigherOrderC3.lean                used by HW33LaurentSimple (indirectly), HW33MultiPole
HW33HigherOrderC4.lean                used by HW33HigherOrderAuto
HW33HoloCancel.lean                   used by HW33LaurentSimple, HW33PVSing
HW33LaurentPolarPart.lean             used by HW33LaurentSimple, HW33PVSing, HW33Tight
HW33LaurentSimple.lean                used by HW33Clean
HW33Monotonicity.lean                 used by HW33Final
HW33MultiPole.lean                    used by HW33Closed, HW33HigherOrderAvoidance
HW33Paper.lean          126 lines   used by HW33HigherOrderAvoidance, HW33SimpleClean
HW33PVSing.lean                       used by HW33SimpleClean
HW33SectorEven.lean                   used by HW33Closed, HW33LaurentPolarPart
HW33SimpleClean.lean    601 lines   used by HW33Clean
HW33Tight.lean                        used by HW33Paper
```

**Conclusion**: `HW33Clean.lean` is the "headline" (terminal) file — only one orphan in the chain. The others are NOT stale; they form a connected internal-dependency graph feeding into `HW33Clean.lean`. The memory note about HW33 consolidation in HW33Clean.lean is consistent: HW33Clean is the user-facing endpoint, the rest are tier-1 dependencies. **No HW33* file is stale**.

(However, the chain's depth and breadth — 21 files, ~3500+ lines, deeply nested cancellation/avoidance variants — is a candidate for major **internal consolidation** if/when the HW 3.3 theorem stabilizes for upstream PR.)

### ValenceFormula trio

| File | Lines | Role |
|------|-------|------|
| `ValenceFormula.lean` | 367 | Orbit-sum form, conditional on `valence_formula_orbit_sum`; imports `CanonicalReps`. Building block. |
| `ValenceFormulaBridged.lean` | 170 | Combines unconditional residue/modular side `HasCauchyPVOn` bridges to give axiom-clean Tendsto'd version. |
| `ValenceFormulaFinal.lean` | 70 | The user-facing one-liner: `valence_formula_textbook` taking only `hf : f ≠ 0`. |

This is **NOT proliferation** — it's a deliberate three-layer architecture (intermediate / bridged / final). All three are necessary in the current setup. ValenceFormulaFinal is the headline; the other two are dependencies. **Keep all three**.

### Residue duplication

Two files define `HasSimplePoleAt`:

- `LeanModularForms/ForMathlib/Residue.lean` (97 lines) — legacy chain
- `LeanModularForms/ForMathlib/GeneralizedResidueTheory/Residue.lean` (760 lines) — generalized residue theory chain

The HungerbuhlerWasem.lean docstring **explicitly flags** the duplication:

> "The project currently maintains two parallel residue libraries with overlapping root-namespace identifiers (e.g. both `LeanModularForms.ForMathlib.Residue` and `LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue` define `HasSimplePoleAt`...) This file commits to the legacy chain..."

This is a known parallel-libraries situation requiring unification. **Major consolidation candidate** (out of scope for Phase 7, but the duplication should be tracked).

### BoundaryWinding "Proof" files

`BoundaryWindingArcProof.lean` (355), `BoundaryWindingSeg1Proof.lean` (269), `BoundaryWindingSeg4Proof.lean` (286), `SmoothBoundaryWindingProof.lean` (219) are all real, internally connected, and used by `ArcGenericFTCProvider`, `Seg1FTCProvider`, `Seg4FTCProvider`, `FDWindingDataFullAssembly`. The `*Proof` suffix is suspicious-looking but the files are genuine contour-integration content. **Keep**.

## H. Top recommendations for removal/consolidation (prioritized)

### Tier 1: Immediate deletion (~1620 lines, zero downstream impact)

These files compile to NOTHING (entire body is a `/- ... -/` block comment) and are not imported by anything:

1. **`hassumunifon.lean`** (1023 lines) — fix-or-delete; biggest single win
2. **`Bounds.lean`** (340 lines) — entire body commented
3. **`IsBoundedAtImInfty.lean`** (78 lines) — entire body commented
4. **`LevelOne.lean`** (55 lines) — entire body commented
5. **`Identities.lean`** (40 lines) — entire body commented (but transitively imported by `IsBoundedAtImInfty`, `LevelOne`, `QExpansion`, `CongruenceSubgrps`-importing files; those imports also need to die)
6. **`CongruenceSubgroupsCopy.lean`** (15 lines) — explicit placeholder stub, docstring says "retained as empty placeholder"; nothing imports it

Also fully commented but the file may still appear in another import (verify):
7. **`Petersson.lean`** — full body commented; imported by `Bounds.lean` (also dead)
8. **`QExpansion.lean`** — full body commented; imported by `Petersson` (dead) and `LevelOne` (dead) and `Identities` (dead). Likely transitively orphan in real terms.

### Tier 2: Orphan files with real content (delete if no plans to use)

9. **`WindingHomotopy.lean`** — superseded by `GeneralizedResidueTheory.Homotopy.*` chain
10. **`ResidueSideProof.lean`** — old chain artifact; covered by `ValenceFormulaBridged`
11. **`Cycles.lean`** — orphan contour-cycle API; no callers
12. **`HorizontalContribution.lean`** — orphan seg5 horizontal-line contribution; integrate into ValenceFormula chain or delete

### Tier 3: Dead-private cleanup (~24 declarations)

Mechanical pass: remove the 24 dead private/unused declarations enumerated in Section B. Each removal is small and safe.

### Tier 4: Structural consolidation (defer, but track)

13. **Unify the two Residue libraries** — `Residue.lean` vs `GeneralizedResidueTheory.Residue.lean` both define `HasSimplePoleAt`. Pick one and migrate dependents.
14. **HW33 chain consolidation** — 21 files connected for one theorem; reasonable target for split-file rework once API stabilizes.
15. **ForMathlib PR pipeline** — files like `UpperHalfPlane.lean`, `FunctionsBoundedAtInfty.lean`, `AtImInfty.lean`, `SlashActions.lean`, `TrigLemmas.lean`, `Instances.lean`, `CongruenceSubgrps.lean` are all PR-ready or near-PR-ready upstream candidates.

### Summary

- **~6-8 files to delete outright** (Tier 1): immediate, mechanical, ~1600 lines.
- **~4 more files to delete** (Tier 2) after verifying no downstream callers.
- **~24 dead private declarations** to clean up (Tier 3).
- **Two structural projects** to track (Tier 4).
