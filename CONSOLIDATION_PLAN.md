# LeanModularForms Consolidation Plan

**Generated**: 2026-05-22
**Branch**: `feat/mathlib-prs`
**Project size at write time**: 75,022 lines across 210 `.lean` files (already -4,800 from the post-overview baseline).
**User target**: 20,000 lines (≈ -55,000, -73% reduction from current).
**Goal**: a strategic roadmap that gets from 75k → close to 20k without regressing the two protected theorems (`valence_formula_textbook`, `hw_3_3_clean_full_mero`).

Supersedes the action lists in `PROJECT_OVERVIEW.md` (now ~30% executed) and the curve-unification ambitions in `P4_PLAN.md` (Phases 1-3 landed; Phase 4 deferred).

---

## TL;DR for the impatient

| Lever | Realistic LOC saving | Effort |
|---|---|---|
| **A. Drop subsystems not load-bearing for the two protected theorems** | **-14,300** (one-day audit) | Low |
| **B. Mathlib upstreaming (6 PRs)** | -200 local + huge qualitative | 1-2 weeks |
| **C. Proof golfing of the 595 long proofs** | -10,000 to -15,000 | 4-6 weeks |
| **D. Variant-ratchet collapse + common generalisations** | -3,500 to -5,000 | 2-3 weeks |
| **E. New API abstractions** | -2,000 to -4,000 | 2-3 weeks |
| **F. WIP/stub cleanup** | -1,200 | 1-2 days |
| **G. Inline single-use lemmas** | -1,000 to -2,000 | 1 week |
| **Realistic floor (with significant work)** | **30,000-35,000 lines** | 8-12 weeks |
| **User's stated 20k target** | very hard; requires structural drop of the GRT generality | a research-level decision |

**Honest verdict: 20k is achievable only if we are willing to scope down to the literal smallest proof of the two protected theorems and forfeit the generality the GRT subsystem offers.** A more realistic "high-quality mathlib-shaped" floor is **30k-35k lines**. See Part 5 for the cost-benefit case for each subtraction.

---

## Part 1 — Inventory of the current state

### 1.1 Top-level structure

```
LeanModularForms.lean                     # umbrella; imports ~110 of 210 files
LeanModularForms/
├── ForMathlib/                           # 28,836 lines  (analytic infrastructure)
│   ├── HungerbuhlerWasem/                # 14,591 lines  (HW3.3 driver subdir)
│   ├── ValenceFormula/                   #  8,546 lines  (Diamond-Shurman valence)
│   ├── GeneralizedResidueTheory/         #  9,697 lines  (the GRT subsystem)
│   ├── ContourIntegral/                  #    529 lines  (4 small files)
│   └── (root)                            # ~33,500 lines (HW33*.lean fan-out,
│                                         #                Dixon, FD-boundary,
│                                         #                Piecewise C¹ types, etc.)
├── Modularforms/                         # 11,542 lines  (modular-form objects)
└── SpherePacking/                        #  1,281 lines  (Viazovska scaffolding)
```

### 1.2 Top 30 largest files (sorted by size)

| Rank | Lines | File | 1-line role |
|---|---|---|---|
| 1 | 4,803 | `ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean` | Multi-crossing CPV main theorem; 4 proofs >280 lines each |
| 2 | 2,294 | `ForMathlib/HungerbuhlerWasem/Crossing.lean` | Single-crossing residue theorem; 16 variants |
| 3 | 1,383 | `Modularforms/summable_lems.lean` | Summability lemmas for q-expansion / Eisenstein |
| 4 | 1,348 | `ForMathlib/PaperPwC1Immersion.lean` | Paper-faithful closed immersion + cyclic shift |
| 5 | 1,338 | `ForMathlib/HungerbuhlerWasem/LocalCutoffs.lean` | Per-window CPV cutoff machinery |
| 6 | 1,265 | `ForMathlib/HungerbuhlerWasem/CrossingDataBuilder.lean` | Constructs `SingleCrossingData` for poles |
| 7 | 1,218 | `ForMathlib/HungerbuhlerWasem/CPVExistence.lean` | CPV exists for crossing curves |
| 8 | 1,113 | `ForMathlib/CornerFTCAtRho.lean` | FTC at the `ρ` corner of the FD |
| 9 | 1,071 | `Modularforms/JacobiTheta.lean` | `Θ₂/₃/₄`, `H₂/₃/₄` and q-expansions |
| 10 | 1,037 | `Modularforms/FG.lean` | Auxiliary forms `F`, `G`; 8 sorries; no external consumers |
| 11 |   954 | `ForMathlib/ValenceFormula/WindingWeights/I.lean` | gWN = -1/2 at `i` |
| 12 |   937 | `ForMathlib/GeneralizedResidueTheory/WindingNumber/CrossingAnalysis.lean` | (ORPHAN - no consumers) |
| 13 |   904 | `Modularforms/Eisenstein.lean` | `E₄`, `E₆` |
| 14 |   859 | `SpherePacking/ViazovskaMagicFunction.lean` | (ORPHAN - commented out in barrel) |
| 15 |   855 | `ForMathlib/ValenceFormula/OnCurvePV/Main.lean` | OnCurvePV for valence formula |
| 16 |   812 | `ForMathlib/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean` | Sector-curve technical lemma |
| 17 |   810 | `ForMathlib/ArcGenericFTCProvider.lean` | Generic arc-piece FTC |
| 18 |   793 | `ForMathlib/PaperPwC1ImmersionInvariance.lean` | Paper-faithful invariance lemmas |
| 19 |   793 | `ForMathlib/HungerbuhlerWasem/LaurentExtraction.lean` | Laurent-polar-part extraction |
| 20 |   779 | `ForMathlib/HigherOrderAssembly.lean` | Higher-order pole assembly |
| 21 |   739 | `Modularforms/Derivative.lean` | Serre derivative; 1 sorry |
| 22 |   721 | `ForMathlib/ValenceFormula/WindingWeights/RhoPlusOne.lean` | gWN = -1/2 at `ρ+1` |
| 23 |   711 | `ForMathlib/ValenceFormula/PVChain/Assembly.lean` | PV-chain assembly |
| 24 |   711 | `ForMathlib/DixonTheorem.lean` | Dixon's theorem; 13 variants |
| 25 |   702 | `ForMathlib/ValenceFormula/Boundary/Smooth.lean` | Smooth FD boundary contribution |
| 26 |   701 | `ForMathlib/HungerbuhlerWasem.lean` | HW top-level barrel |
| 27 |   693 | `ForMathlib/ValenceFormula/WindingWeights/Rho.lean` | gWN = -1/2 at `ρ` |
| 28 |   655 | `ForMathlib/DixonDiff.lean` | Differentiability lemmas for Dixon proof |
| 29 |   621 | `ForMathlib/HungerbuhlerWasem/HigherOrderAsymptotics.lean` | Higher-order CPV asymptotics |
| 30 |   619 | `ForMathlib/WindingInteger.lean` | Integer-valued winding numbers |

Total in top-30: **~30,000 lines** (40% of the project).

### 1.3 Per-namespace LOC

| Namespace | Lines | Role |
|---|---|---|
| `ForMathlib/HungerbuhlerWasem/` | 14,591 | HW3.3 driver (single + multi crossings, Laurent extraction, higher order) |
| `ForMathlib/` (root) | 28,836 | Mixed: HW33*.lean cluster (~3,400), Dixon (~1,500), curve types (~3,200), FD-boundary (~1,200), Valence support (~5,000+) |
| `ForMathlib/ValenceFormula/` | 8,546 | Modular-side / residue-side / winding weights of the valence formula |
| `ForMathlib/GeneralizedResidueTheory/` | 9,697 | The "GRT" subsystem (general residue/PV theory) |
| `Modularforms/` | 11,542 | Modular-form objects (Δ, E_k, η, Θ, FG, …) |
| `SpherePacking/` | 1,281 | Viazovska magic-function scaffolding |
| **Total** | **75,022** | |

### 1.4 Top files classified by load-bearing status

| File | Lines | Status | Notes |
|---|---|---|---|
| `MultiCrossingCPV.lean` | 4803 | LOAD-BEARING | Required by `hw_3_3_clean_full_mero` |
| `Crossing.lean` | 2294 | LOAD-BEARING | But ~849 lines already private-marked & deletable; still 16 variants visible |
| `summable_lems.lean` | 1383 | DROP CANDIDATE | Only consumers are other Modularforms files; no consumer outside the FG cluster |
| `PaperPwC1Immersion.lean` | 1348 | LOAD-BEARING | Curve type used by HW3.3 |
| `LocalCutoffs.lean` | 1338 | LOAD-BEARING | |
| `CrossingDataBuilder.lean` | 1265 | LOAD-BEARING | |
| `CPVExistence.lean` | 1218 | LOAD-BEARING | |
| `CornerFTCAtRho.lean` | 1113 | LOAD-BEARING | Needed by valence formula |
| `JacobiTheta.lean` | 1071 | DROP CANDIDATE | Not in dep chain of either protected theorem |
| `FG.lean` | 1037 | DROP CANDIDATE | 8 sorries, self-contained, no external consumer |
| `WindingWeights/I.lean` | 954 | LOAD-BEARING | Required by valence formula |
| `GRT/WindingNumber/CrossingAnalysis.lean` | 937 | **DROP — fully ORPHANED** | Confirmed zero importers in project |
| `Eisenstein.lean` | 904 | DROP CANDIDATE | Not in either dep chain |
| `ViazovskaMagicFunction.lean` | 859 | **DROP — fully ORPHANED** | Commented out in `LeanModularForms.lean` umbrella |
| `OnCurvePV/Main.lean` | 855 | LOAD-BEARING | Valence formula |
| `SectorCurveLemma.lean` | 812 | LOAD-BEARING (via GRT) | |
| `ArcGenericFTCProvider.lean` | 810 | LOAD-BEARING | |
| `PaperPwC1ImmersionInvariance.lean` | 793 | LOAD-BEARING | |
| `LaurentExtraction.lean` | 793 | LOAD-BEARING | |
| `HigherOrderAssembly.lean` | 779 | LOAD-BEARING (HW3.3 multi-pole branch) | |
| `Derivative.lean` | 739 | DROP CANDIDATE | 1 sorry, only used by FG.lean cluster |
| `WindingWeights/RhoPlusOne.lean` | 721 | LOAD-BEARING | |
| `PVChain/Assembly.lean` | 711 | LOAD-BEARING | |
| `DixonTheorem.lean` | 711 | LOAD-BEARING | 13 variants — keep canonical + alias |
| `Boundary/Smooth.lean` | 702 | LOAD-BEARING | |
| `HungerbuhlerWasem.lean` | 701 | LOAD-BEARING (barrel) | |
| `WindingWeights/Rho.lean` | 693 | LOAD-BEARING | |
| `DixonDiff.lean` | 655 | HELPER | Differentiability infra for Dixon |
| `HigherOrderAsymptotics.lean` | 621 | LOAD-BEARING | |
| `WindingInteger.lean` | 619 | LOAD-BEARING | |

The classification of "DROP CANDIDATE" is grounded in Part 2's dependency walk.

---

## Part 2 — Dependency walk

### 2.1 Method

Computed transitive imports from the two protected theorems using a Python walker over `import LeanModularForms.…` lines:
- Seeds: `LeanModularForms.ForMathlib.ValenceFormulaFinal`, `LeanModularForms.ForMathlib.HW33Clean`
- Union of closures: **149 files, 60,708 lines** (the "required set")
- Project total: 210 files, 75,022 lines
- **Orphans (not in required set): 50 files, 14,314 lines (19.1% of the project)**

The walker was conservative: it includes any file reached by any chain of `import` statements from either seed. A file is "orphan" only if it is reachable from neither.

### 2.2 The 50 orphaned files (sorted by size)

```
1383  Modularforms/summable_lems.lean
1071  Modularforms/JacobiTheta.lean
1037  Modularforms/FG.lean                          (8 sorries)
 937  GRT/WindingNumber/CrossingAnalysis.lean        # transitively orphaned in GRT itself
 904  Modularforms/Eisenstein.lean
 859  SpherePacking/ViazovskaMagicFunction.lean
 739  Modularforms/Derivative.lean                  (1 sorry)
 564  Modularforms/Generators/Injectivity.lean
 480  Modularforms/Delta.lean
 472  Modularforms/ThetaDerivIdentities.lean
 421  Modularforms/ResToImagAxis.lean
 409  Modularforms/DimensionFormulas.lean           (1 sorry)
 373  SpherePacking/CuspDecay.lean
 329  Modularforms/Eisensteinqexpansions.lean
 299  Modularforms/SlashActionAuxil.lean
 264  Modularforms/tsumderivWithin.lean
 255  Modularforms/EisensteinAsymptotics.lean
 233  Modularforms/Generators/Surjectivity.lean
 222  Modularforms/NormNumI.lean
 222  GRT/WindingNumber/Decomposition.lean           # transitively orphaned
 209  Modularforms/Generators/Defs.lean
 194  GRT/WindingNumber/Defs.lean                    # used by Proposition2_2 only — keep
 184  Modularforms/clog_arg_lems.lean
 181  Modularforms/E2.lean
 179  Modularforms/IsCuspForm.lean
 176  Modularforms/iteratedderivs.lean
 175  Modularforms/eta.lean
 149  Modularforms/BigO.lean
 141  Modularforms/RamanujanIdentities.lean
 127  Modularforms/qExpansion_lems.lean
 121  Modularforms/SerreDerivativeSlash.lean
 109  Modularforms/Cauchylems.lean
  99  Modularforms/csqrt.lean
  94  Modularforms/PhiTransform.lean
  86  Modularforms/QExpansion.lean
  79  Modularforms/uniformcts.lean
  78  Modularforms/multipliable_lems.lean
  71  ForMathlib/CongruenceSubgrps.lean             # narrow upstreamable helper
  51  Modularforms/Icc_Ico_lems.lean
  49  SpherePacking/PhiHolomorphic.lean
  46  Modularforms/equivs.lean
  43  Modularforms/AtImInfty.lean
  39  ForMathlib/SlashActions.lean
  37  Modularforms/riemannZetalems.lean
  36  Modularforms/exp_lems.lean
  34  Modularforms/MDifferentiableFunProp.lean
  21  Modularforms/upperhalfplane.lean
  15  ForMathlib/UpperHalfPlane.lean
  13  ForMathlib/FunctionsBoundedAtInfty.lean
   5  Modularforms/Generators.lean
```

Subtotals by namespace:
- `Modularforms/` orphans: 11,542 / 11,542 lines (**100% of Modularforms namespace is orphaned w.r.t. protected theorems**)
- `SpherePacking/` orphans: 1,281 / 1,281 lines (**100% orphaned**)
- `GRT/WindingNumber/{CrossingAnalysis,Decomposition}`: 1,159 lines (the WindingNumber subdir minus `Proposition2_2` and `Defs`)
- Small `ForMathlib/` upstreamables: 138 lines (UpperHalfPlane, FunctionsBoundedAtInfty, SlashActions, CongruenceSubgrps)

This is the single biggest finding of the audit.

### 2.3 Why is Modularforms orphaned?

The valence formula's statement uses `ModularForm Γ(1) k` and `f ≠ 0`, but its proof goes through `CoreIdentityProof.lean → ValenceFormula.lean → CanonicalReps.lean → Orbits.lean → EllipticPoints.lean` plus `ModularInvariance.lean`. None of this touches `Δ`, `E₄`, `E₆`, `J`, `η`, `Θ`, summable lemmas, or `FG`. The mathlib `ModularForm` infrastructure provides everything needed for the statement. The local `Modularforms/` namespace is *infrastructure that was developed in parallel for a separate goal* (Ramanujan identities, dimension formulas, the FG monotonicity programme, the generators-of-SL₂(ℤ) work).

This subsystem is mathematically valuable, but **it is not what the user pays for if their target is HW3.3 + valence formula.**

### 2.4 The required-set structure

149 required files, top 6 subgroups (LOC):

| Subgroup | Lines | Role |
|---|---|---|
| `ForMathlib/HungerbuhlerWasem/` | 14,591 | HW3.3 driver |
| `ForMathlib/` root files in dep chain | 22,000+ | Mixed |
| `ForMathlib/ValenceFormula/` | 8,546 | Valence formula machinery |
| `ForMathlib/GeneralizedResidueTheory/` (minus orphans) | 8,538 | GRT (without the unused WindingNumber files) |
| `ForMathlib/ContourIntegral/` | 529 | Small thin layer |

---

## Part 3 — Reduction levers

### Lever A. Drop entire subsystems not load-bearing

This is the single largest immediate saving. Three subsystems are 100% orphaned:

**A1. `Modularforms/`** (11,542 lines, 40 files)
- All of `summable_lems.lean`, `JacobiTheta.lean`, `FG.lean`, `Eisenstein.lean`, `Derivative.lean`, `Delta.lean`, `ResToImagAxis.lean`, `DimensionFormulas.lean`, the `Generators/` subdirectory (1006 lines across 4 files), the η/Θ/E₂/E_k cluster, plus 25 small files.
- Eliminates all 10 sorries in the project.
- Cost: loses the FG monotonicity programme, dimension formulas for `M_k(Γ)`, the Ramanujan identity work, and the generator-of-SL₂(ℤ) work. None of these is used by either protected theorem.
- Action: move to a sibling repo (`LeanModularForms-modularforms` or contribute to mathlib's `ModularForm` namespace) or simply prune.
- **Saving: -11,542 lines**.

**A2. `SpherePacking/`** (1,281 lines, 3 files)
- Already commented out in `LeanModularForms.lean` (`CuspDecay` and `ViazovskaMagicFunction` are noted as "name collision with EisensteinAsymptotics" and "transitively imports CuspDecay"). `PhiHolomorphic.lean` is the only active file (49 lines) and it has no consumers either.
- Saving: -1,281 lines.

**A3. `GRT/WindingNumber/{CrossingAnalysis,Decomposition}.lean`** (1,159 lines, 2 files)
- Confirmed zero importers in the entire project. Speculative infrastructure that never landed in the HW3.3 chain.
- Saving: -1,159 lines.

**A4. Small upstreamables outside Modularforms** (138 lines)
- `ForMathlib/UpperHalfPlane.lean` (15), `FunctionsBoundedAtInfty.lean` (13), `SlashActions.lean` (39), `CongruenceSubgrps.lean` (71). All small, all earmarked for mathlib in PROJECT_OVERVIEW.md. Each is one mathlib PR.
- Saving: -138 lines (once mathlib accepts).

**Lever A total: -14,120 lines**. Effort: 1-2 days (most of it is `git rm` + lake build verification).

### Lever B. Mathlib upstreaming

Beyond Lever A, infrastructure that lives in the dep chain but morally belongs upstream:

1. **`HasGeneralizedWindingNumber`** + foundational lemmas (`.eq`, `.unique`, `.neg`). Currently 203 lines in `ForMathlib/GeneralizedWindingNumber.lean`. Once upstream: this file becomes ~30 lines of project-specific wrappers. **Saving: ~170 lines.**
2. **`HasCauchyPV` / `HasCauchyPVOn`**. 242 lines in `ForMathlib/CauchyPrincipalValue.lean`. Upstreamable as a `MeasureTheory.CauchyPV` namespace. **Saving: ~200 lines locally after upstream.**
3. **`MeromorphicAt.logDeriv_meromorphicOrderAt_eq_neg_one_of_…`**. One missing named lemma in mathlib (PROJECT_OVERVIEW.md §A4); collapse `MeromorphicBridge.lean` (187 lines) to a few simp lemmas. **Saving: ~150 lines.**
4. **`Path.trans₅` / `Path.transAll`**. The 5-fold concatenation needed by `FDBoundaryH.lean`. Generic combinator. **Saving: ~50 lines + unlocks Phase 4 of P4_PLAN.md.**
5. **Trig identities**: `exp_real_angle_I`, `cos/sin_two_pi_div_three` (`ForMathlib/TrigLemmas.lean`, 30 lines). **Saving: ~25 lines.**
6. **`PiecewiseC1Path`** itself, once the type unification (P4) is fully stable. Currently 137 lines of definition, ~200 lines of infrastructure scattered. Long-term, the project keeps a 20-line shim. **Saving: ~300 lines after upstream.**

**Lever B total: -700 to -900 lines locally** plus enormous *qualitative* benefit (downstream proofs collapse on mathlib idioms). Effort: 6 PRs, ~2 weeks per PR end-to-end (including review cycles). Realistic horizon: 2-4 months.

### Lever C. Proof golfing

Hard numbers:

- 595 proofs in the project are ≥ 30 lines (out of ~2,065 named declarations).
- Those 595 proofs together account for **36,361 lines (48% of the project)**.
- The top 20 proofs alone are 8,065 lines.

Distribution:
- 30-49 lines: 356 proofs
- 50-99 lines: 179 proofs
- 100-199 lines: 42 proofs
- 200-399 lines: 16 proofs
- 400+ lines: 2 proofs (one is 528 lines: `perCrossing_higherOrder_window_integral_tendsto`)

**Estimated reduction per category (based on a sample of three proofs):**

- 30-49 lines: typical reduction 20-30% via mathlib-idiom alignment, `gcongr`, `fun_prop`, `omega` over `linarith`. Estimated saving: 356 × ~10 lines = **~3,500 lines**.
- 50-99 lines: typical 25-35%; saving ≈ 179 × ~20 lines = **~3,500 lines**.
- 100-199 lines: typical 30-40% (high payoff from extracting common sub-lemmas); saving ≈ 42 × ~50 lines = **~2,000 lines**.
- 200+ lines: 50-60% reduction is realistic if decomposed (see e.g. the recent wave-8 work `ba73a1cc` "break up 3 large internal helpers"). Saving ≈ 18 × ~150 lines = **~2,700 lines**.

**Lever C total: -10,000 to -15,000 lines.** Effort: 4-6 weeks of focused per-file `/cleanup` orchestrated via `/cleanup-all`. The orchestrator-worker pattern from the 187-batch `/cleanup-all` run is well suited (see `mathlib-quality:cleanup-all` skill).

**Why high payoff?**
- The user's recent commits already show this pattern at work: 8 waves of "decompose: break up N more long proofs" lowered the relevant files significantly.
- The two giant CPV proofs in `MultiCrossingCPV.lean` (528-line and 484-line) are prime candidates: at 50% golf each, that's -500 lines from two proofs alone.

### Lever D. Common generalisations / variant ratchet collapse

Concrete clusters identified:

- **`residueTheorem_crossing_*`** in `HungerbuhlerWasem/Crossing.lean`: currently 16 visible (down from 32; the recent `781e02f` commit `refactor(P3a)` removed 849 lines by private-marking and deleting unused variants). **Remaining saving: -300 to -500 lines** by promoting two canonical statements and dropping more aliases.
- **`hw_3_3_clean*`** in `HW33Clean.lean`: 8 variants in a single file. Replace 7 of them with `alias` / `abbrev` / one-line wrappers around `hw_3_3_clean_full_mero`. **Saving: -200 lines.**
- **`dixonFunction_eq_zero*`** in `DixonTheorem.lean`: 12 visible variants. Promote `_of_nullHomologous_convex_full` as canonical; alias the rest. **Saving: -200 to -300 lines.**
- **HW33 fan-out files** (`HW33Clean`, `HW33Tight`, `HW33Paper`, `HW33SimpleClean`, `HW33LaurentSimple`, `HW33LaurentPolarPart`, `HW33PVSing`, `HW33HoloCancel`, `HW33HigherOrder`, `HW33MultiPole`): 10 files totalling 3,421 lines. Merge into 3 thematic files (paper, multi-pole, higher-order). **Saving: -800 lines.**
- **Side-mirror pairs**:
  - `BoundaryWindingSeg{1,4}Proof.lean` — partly done in `544814e` (P2a). Remaining: factor remaining duplication, **-50 to -100 lines**.
  - `Seg{1,4}FTCProvider.lean` and `VertSegFTCProvider.lean`: `3daf7fa` (P2b) extracted shared helper -136 lines. Still 1,023 combined lines; could go further to -300.
  - `CrossingAt{I,Rho}.lean`, `ArcFTC{AtI,Generic}.lean`: parametrise over elliptic point. **-300 lines** if fully done.
- **`WindingWeights/{I,Rho,RhoPlusOne}.lean`** (954+693+721 = 2,368 lines): the three files are structural twins for the three orbifold points. Parametrise over an `EllipticPoint` argument. **Saving: -1,000 lines**.
- **`CornerFTCAtRho.lean` (1,113) vs `CornerFTCAtI.lean`** (if it exists separately): parametrise. **Saving: -300 to -500 lines.**

**Lever D total: -3,500 to -5,000 lines.** Effort: 2-3 weeks. Risk: each elliptic-point parametrisation touches a protected theorem proof; careful axiom checking required (the user is now experienced with this from the recent waves).

### Lever E. New API abstractions

Each adds one new abstraction whose downstream effect is to shorten many proofs:

- **`PiecewiseC1Path.concat`** + 5-fold variant. Estimated 80 lines of API. Downstream effect: `FDBoundaryH.lean`'s nested-`if` cascade collapses, `Path.trans₅` is no longer needed, ~12 callers of `fdBoundaryFun` simplify their `simp only [fdBoundaryFun, show ¬t ≤ k/5 ...]` pattern. **Net saving: -300 to -500 lines.**
- **`WindingNumberData`** bundle. Today the project carries `gWN`, the `curve_avoids_outside`, the `crossing_data` etc. as separate hypotheses across many lemmas. Bundling gives ~50 callers a one-line API. **Net saving: -200 lines.**
- **`CauchyPVOn` typeclass alignment**. `cauchyPrincipalValueOn` and `HasCauchyPVOn` co-exist (PROJECT_OVERVIEW.md §3.3). Pick one, route everything through it. **Saving: -200 lines.**
- **Generic `_at_singular_point` API for elliptic-point lemmas**. Replaces the three `_at_i / _at_rho / _at_rho_plus_one` triples noted in CLEANUP_PLAN.md Phase C. Coordinates with Lever D's parametrisation. **Saving: -400 lines (incremental over Lever D).**
- **Bundled `FDWindingData`** projection layer. The current `FDWindingDataFullSeg1Seg4.lean` + `FDWindingDataFullAssembly.lean` (134+103 lines) is glue; a cleaner projection-based API would let the projection layer shrink. **Saving: -100 lines.**
- **`HasSimplePoleAt` → `MeromorphicAt + meromorphicOrderAt = -1`** redefinition. Already proposed in PROJECT_OVERVIEW.md §3.1, §3.2. Collapses `Residue.lean` (62 lines), `PrincipalPart.lean` (174 lines), large parts of `MeromorphicBridge.lean` (187 lines). **Saving: -300 lines after.**

**Lever E total: -1,500 to -2,500 lines.** Effort: 2-3 weeks. Risk: medium; each abstraction touches a sizable number of files but the touch is uniform.

### Lever F. WIP / stub cleanup

- **`Modularforms/FG.lean`** (1,037 lines, 8 sorries). **Drop entirely** as part of Lever A1. No standalone WIP cleanup needed.
- **`Modularforms/Derivative.lean`** (739 lines, 1 sorry on `antiSerreDerPos`). Drop with Lever A1.
- **`Modularforms/DimensionFormulas.lean`** (409 lines, 1 sorry on finite-dimensionality for arbitrary finite-index Γ). Drop with Lever A1.

After Lever A, **all 10 project sorries are gone in one stroke** (currently in 3 files, all within `Modularforms/`).

Other small WIP detritus inside the required set:
- `set_option backward.isDefEq.respectTransparency false in` on 2 lines in `DslopeIntegral.lean` (PROJECT_OVERVIEW.md flagged this). Investigate whether it's still needed; if not, remove. **Saving: 2 lines + cleaner code.**
- The `attribute [local instance] Classical.propDecidable` in `CoreIdentityProof.lean` — likely fixable by adjusting one lemma's classical reasoning. **Saving: tiny but cleanliness.**

**Lever F total: -1,200 lines** (mostly absorbed by Lever A).

### Lever G. Inline single-use lemmas

A targeted pass finds lemmas called 1-2 times where the saving (lemma signature + name + boilerplate) exceeds the gain from naming.

Empirically across the recent waves, this has been worth ~5% on the files touched. Across the post-Lever-A required set (~46,000 lines), that's:

**Lever G total: -1,000 to -2,000 lines.** Effort: 1 week, mechanical, low risk.

### Summary of levers

| Lever | Conservative | Optimistic | Effort |
|---|---|---|---|
| A. Drop subsystems | -14,300 | -14,300 | 1-2 days |
| B. Mathlib upstreaming | -700 | -900 | 2-4 months |
| C. Proof golfing | -10,000 | -15,000 | 4-6 weeks |
| D. Variant ratchet + generalisations | -3,500 | -5,000 | 2-3 weeks |
| E. New API abstractions | -1,500 | -2,500 | 2-3 weeks |
| F. WIP cleanup (subsumed by A) | 0 (already in A) | 0 | n/a |
| G. Inline single-use | -1,000 | -2,000 | 1 week |
| **Total** | **-31,000** | **-39,700** | **~10-14 weeks of focused work** |

Starting from 75k:
- Conservative landing: **44,000 lines** (-42%)
- Optimistic landing: **35,000 lines** (-53%)

To reach 20k, we would need an *additional* -15,000 lines beyond the optimistic landing. The only place this can come from is by removing parts of the GRT subsystem or the entire valence formula chain — a decision about which result the project should actually deliver.

---

## Part 4 — Phased plan with concrete targets

Each phase is independently shippable: after each phase, the build is green and both protected theorems are axiom-clean.

### Phase 1: Drop the orphan subsystems (Lever A)

**Goal**: remove every file that is not in the transitive dependency closure of `valence_formula_textbook` ∪ `hw_3_3_clean_full_mero`.

**Files affected**: 50 files across `Modularforms/`, `SpherePacking/`, `GRT/WindingNumber/{CrossingAnalysis,Decomposition}`, and 4 small `ForMathlib/` files.

**Procedure**:

1. Generate the official "required" file list (use the Python walker in this plan, or `lake env lean --print-deps` equivalent).
2. Stash the `Modularforms/` subtree to a sibling branch `archive/modularforms-namespace` for future revival. Same for `SpherePacking/` (stash to `archive/sphere-packing`).
3. `git rm` each orphan file.
4. Update `LeanModularForms.lean` umbrella: remove all `import LeanModularForms.Modularforms.*` and `import LeanModularForms.SpherePacking.*` lines.
5. Update the four small `ForMathlib/` orphans: prepare upstream mathlib PRs (don't delete yet — they will be deleted *as* the PRs land in `bump-mathlib` cycles).
6. `lake build` (expect green; nothing in the required set imports the orphans).
7. Axiom-check both protected theorems.

**LOC reduction**: -14,120 (Modularforms 11,542 + SpherePacking 1,281 + WN orphans 1,159 + small `ForMathlib` 138).

**Risk**: Low. By construction the deleted files are not in the transitive dependency closure of either protected theorem.

**Effort**: 1 working day (one commit per directory, with axiom verification between).

**Verification protocol**:
```
lake build LeanModularForms 2>&1 | tail -3
# Build completed successfully
```
plus `lean_verify` on `ForMathlib.valence_formula_textbook` and `ForMathlib.hw_3_3_clean_full_mero`. Both must yield `[propext, Classical.choice, Quot.sound]`.

**Note on archiving**: the Modularforms namespace contains substantial mathematical content (Ramanujan identities, MLDE for FG, dimension formulas) that should not be lost. Move to a sibling repo or to mathlib-blueprint contributions. The drop is a *scope decision*, not a deletion of value.

---

### Phase 2: Variant ratchet collapse (Lever D, first pass)

**Goal**: collapse the three named variant clusters (`residueTheorem_crossing_*`, `hw_3_3_clean*`, `dixonFunction_eq_zero*`) and merge the HW33 fan-out files.

**Files affected**:
- `HungerbuhlerWasem/Crossing.lean` (2,294 lines, 16 visible variants)
- `HungerbuhlerWasem/MultiCrossingCPV.lean` (4,803 lines, ~11 variants)
- `HW33Clean.lean` + `HW33Tight.lean` + `HW33Paper.lean` + `HW33SimpleClean.lean` + 6 more HW33 files (3,421 combined)
- `DixonTheorem.lean` (711 lines, 12 variants)

**Procedure**:
1. For each cluster: confirm the canonical statement (already chosen — `_truly_full_spec`, `hw_3_3_clean_full_mero`, `_of_nullHomologous_convex_full`).
2. Promote canonical to `theorem` (currently some are `private`).
3. Convert non-canonical variants to one-line `theorem foo := bar_canonical _ _` aliases or `protected abbrev`.
4. Walk the import graph and delete `private` variants with no remaining in-file callers.
5. Merge HW33 fan-out: target structure
   - `HW33Paper.lean` (paper-faithful statement + 1 line wrappers)
   - `HW33Multi.lean` (multi-pole consolidations)
   - `HW33HigherOrder.lean` (higher-order, already exists)
   - Delete: `HW33SimpleClean.lean`, `HW33Clean.lean`, `HW33Tight.lean`, `HW33HoloCancel.lean`, `HW33LaurentSimple.lean`, `HW33LaurentPolarPart.lean`, `HW33PVSing.lean`, `HW33MultiPole.lean` (inline contents into the new 3-file structure).
6. `lake build`. Axiom check.

**LOC reduction**: -1,500 to -2,500 lines.

**Risk**: Medium. Touches the protected theorems' direct files. Use byte-snapshot of `#print hw_3_3_clean_full_mero` signature as a regression baseline.

**Effort**: 1-2 weeks.

**Verification**: byte-identical signature for `hw_3_3_clean_full_mero`, all 8 `hw_3_3_clean*` variants axiom-clean.

---

### Phase 3: Elliptic-point parametrisation (Lever D, second pass)

**Goal**: parametrise the three structural copies `WindingWeights/I.lean` / `Rho.lean` / `RhoPlusOne.lean` and the related `_at_i / _at_rho / _at_rho_plus_one` triples.

**Files affected**:
- `WindingWeights/I.lean` (954)
- `WindingWeights/Rho.lean` (693)
- `WindingWeights/RhoPlusOne.lean` (721)
- `CornerFTCAtRho.lean` (1,113)
- `ArcFTCAtI.lean` (357), `CrossingAtI.lean` (165), `CrossingAtRho.lean` (496)
- A new `EllipticPoint.lean` file (already exists at 105 lines; extend it)

**Procedure**:
1. Promote `EllipticPoint` from a passive enumeration to an active parameter with its own `WindingWeightData` bundle.
2. Define one parametrised theorem `windingWeight_at_ellipticPoint (P : EllipticPoint) : …`.
3. Specialise `_at_i`, `_at_rho`, `_at_rho_plus_one` as `:= windingWeight_at_ellipticPoint EllipticPoint.i` etc.
4. Delete the three structural-twin files; replace with one shared file plus the three thin specialisations.
5. Same pattern for the `_at_*` FTC/Crossing triples.

**LOC reduction**: -1,000 to -2,000 lines.

**Risk**: Medium-high. The proofs in the three WindingWeights files differ in *which corner of the FD they're integrating around*, and the existing proofs may have subtle case-by-case branches that don't survive parametrisation cleanly. A defensive approach: implement only `WindingWeights/Rho.lean` and `RhoPlusOne.lean` as specialisations of a shared file first (those two are the most similar), keep `I.lean` separate, then revisit.

**Effort**: 2 weeks.

---

### Phase 4: Sidewise-mirror unification (Lever D, third pass)

**Goal**: complete the side-parametrisation work begun in commits `544814e` (P2a) and `3daf7fa` (P2b).

**Files affected**:
- `BoundaryWindingSeg{1,4}Proof.lean` (256+224 lines)
- `Seg{1,4}FTCProvider.lean` (500+523), `VertSegFTCProvider.lean` (207)
- `FDBoundary.lean` (350), `FDBoundaryH.lean` (335), `FDBoundaryReparametrization.lean` (218) — pick `[0,5]` as canonical (PROJECT_OVERVIEW.md §F6)

**Procedure**:
1. Eliminate `FDBoundary.lean` (the `[0,1]` parametrisation). Migrate the 25 callers to `fdBoundaryFun_H`.
2. Eliminate `FDBoundaryReparametrization.lean` outright.
3. Push `BoundaryWindingSeg{1,4}` into a single side-parametrised file.
4. Push `Seg{1,4}FTCProvider` into `VertSegFTCProvider` fully (rather than the partial split currently in place).

**LOC reduction**: -1,000 to -1,500 lines.

**Risk**: Medium-high. The `fdBoundaryFun_H ↔ fdBoundaryFun` migration is the same problem that defeated Phase 4 of `P4_PLAN.md` (twice). It needs the `PiecewiseC1PathOn.concat` prerequisite. Schedule this *after* Phase 5 below.

**Effort**: 2 weeks once `concat` is in place; otherwise 4 weeks.

---

### Phase 5: New API foundations (Lever E)

**Goal**: build the abstractions that unlock Phases 3-4 fully and shorten downstream proofs everywhere.

**Files affected**: new file `PiecewiseC1PathOn/Concat.lean`, modifications to `MeromorphicBridge.lean`, `PrincipalPart.lean`, `Residue.lean`, and `CauchyPrincipalValue.lean`.

**Sub-phases**:

- **5a. `PiecewiseC1PathOn.concat`** (1 week, ~150 lines of new infrastructure). Unblocks Phase 4 and a future mathlib PR (Lever B item 4).
- **5b. Redefine `HasSimplePoleAt`** as `def HasSimplePoleAt f z := MeromorphicAt f z ∧ meromorphicOrderAt f z = -1` (or even an `abbrev`). Collapse the bridge file. (3 days, ~ -200 lines net.)
- **5c. Unify `cauchyPrincipalValueOn` and `HasCauchyPVOn`** (5 days, ~ -100 lines).
- **5d. `WindingNumberData` bundle** (4 days, ~ -150 lines).

**LOC reduction**: -500 to -1,000 (direct) + unlocks Phases 3 and 4.

**Risk**: Medium. Direct touches on the canonical statement of `hw_3_3_clean_full_mero` (it uses `MeromorphicAt` directly already, so the redefinition of `HasSimplePoleAt` is forward-compatible).

**Effort**: 3 weeks.

---

### Phase 6: Mass proof golf (Lever C)

**Goal**: drive the 595 long proofs down by 30-50% on average using `/cleanup-all` orchestration.

**Procedure** (the proven 28-day pattern from sphere packing's `/cleanup-all` skill):
1. Bucket the 595 long proofs by file, then by size.
2. Dispatch per-file Agent calls in waves of 10-20 files each.
3. Each Agent gets one file, one cleanup pass, returns a diff + LOC delta.
4. Orchestrator scoreboards between waves, builds + axiom-checks between batches.
5. After 30-40 batches the project flattens; declare done.

**LOC reduction**: -8,000 to -12,000 lines.

**Risk**: Low-medium per file (build & axiom check after each batch catches regressions). Orchestration is well established.

**Effort**: 4-6 weeks.

---

### Phase 7: Mathlib upstreaming (Lever B)

**Goal**: drive 6 PRs through mathlib review to make the local versions disappear.

**PRs** (each ~ 2 weeks end-to-end):
- B1. `MeromorphicAt.logDeriv_meromorphicOrderAt_eq_neg_one_of_…` (PR-ready locally; small).
- B2. `IsBoundedAtImInfty.neg` + cusp variants (tiny, but unblocks `Modularforms/AtImInfty` if A1 is partial).
- B3. `ModularGroup.modular_S_sq` + width API for `Gamma N`.
- B4. Trig identities (`exp_real_angle_I` etc.).
- B5. `HasGeneralizedWindingNumber` foundations (medium, design discussion needed).
- B6. `HasCauchyPV{On}` (largest, needs API stabilisation first; depends on Phase 5c).

**LOC reduction**: -700 to -900 locally as PRs land.

**Risk**: Low (axiomatic — what lands upstream lands).

**Effort**: 2-4 months calendar time, ~2 working weeks of total active effort.

---

### Summary of the phased plan

| Phase | LOC saved | Effort | Risk | Cumulative |
|---|---|---|---|---|
| 1. Drop orphan subsystems | -14,120 | 1 day | Low | 60,900 |
| 2. Variant ratchet collapse | -2,000 | 1-2 weeks | Medium | 58,900 |
| 3. Elliptic-point parametrisation | -1,500 | 2 weeks | Medium-high | 57,400 |
| 4. Side-mirror unification (FD reparam) | -1,250 | 2-4 weeks | Medium-high | 56,150 |
| 5. New API foundations | -750 | 3 weeks | Medium | 55,400 |
| 6. Mass proof golf | -10,000 | 4-6 weeks | Low-medium | 45,400 |
| 7. Mathlib upstreaming | -800 | 2-4 months calendar | Low | 44,600 |
| **Total** | **-30,420** | **~12-16 weeks active** | | **44,600** |

Realistic landing: **40,000-45,000 lines** (-40% to -45% from current 75k).

To get below 40k requires more aggressive moves (see Part 5).

---

## Part 5 — Honest assessment

### What's the realistic target?

**The user's 20k stated target is, at the current generality of the project, not achievable.**

Here is the line-by-line accounting of why:

| Component | Required for the two protected theorems | Lines (minimum) | Notes |
|---|---|---|---|
| Curve type infrastructure (`PiecewiseC1Path*`, `PwC1Immersion`, etc.) | Yes | 1,000-1,500 | Even after P4 unification |
| FD-boundary parametrisation | Yes (valence formula only) | 1,000-1,500 | Even after unification |
| Generalised winding number + crossings | Yes (HW3.3) | 1,500-2,000 | Even after API redesign |
| Generalised residue theory (GRT) | Yes (HW3.3) | 4,000-5,000 | Even with aggressive golf |
| HW3.3 driver | Yes | 4,000-6,000 | The combinatorics of multi-crossing CPV is genuinely complex |
| Valence formula chain | Yes | 5,000-7,000 | Per-elliptic-point case work even after parametrisation |
| Dixon + Cauchy infrastructure | Yes | 1,000-1,500 | |
| **Subtotal of minimum required** | | **17,500-24,500 lines** | |

The minimum-viable form of just these two theorems, with aggressive consolidation, is **probably 20-25k lines**. The user's target is at the low end of this and only achievable with:

1. Lever A (drop subsystems): mandatory. -14k.
2. Lever C executed aggressively (50%+ golf, not 30-40%): saves another -15k.
3. Lever D + E executed fully: -5k more.

If Levers A+C(aggressive)+D+E land in sequence: **35k → 28k → 23k → 20k**. The 20k target is mathematically achievable but requires every lever to land near the optimistic end.

The 30-35k figure I gave in the TL;DR is for "we did the work but didn't aggressively scope down the GRT generality". To hit 20k, the GRT subsystem itself needs ~50% reduction beyond the orphan removal — and that's where the elliptic-point parametrisation (Phase 3) and aggressive golf (Phase 6) must compound.

### Cost-benefit per phase

| Phase | LOC/day | Strategic value | Recommendation |
|---|---|---|---|
| 1 | 14,120 / 1 | Massive | **Do first, always.** |
| 2 | ~200/day | Medium-high | Do second; tidies the public API. |
| 3 | ~125/day | Medium-high | Risky but needed to break 35k. |
| 4 | ~80/day | Medium | Skip if running short on time. |
| 5 | ~40/day | Medium (enabler, not direct) | Do *before* 3 and 4. |
| 6 | ~250/day with orchestration | Largest absolute saving | Treat as the workhorse. |
| 7 | ~10/day local | Strategic (mathlib presence) | Do in parallel with 6. |

Top-3 levers by total LOC: **C (golf), A (drop), D (variants)**.
Top-3 levers by LOC-per-day: **A (drop), C (golf), F (subsumed)**.
Top-3 levers by qualitative gain: **B (upstream), E (API), D (variants)**.

### What should be DEFERRED because the payoff is too small?

- **Lever B6 (`HasCauchyPV` to mathlib)**: high effort, depends on the project's own design first stabilising. Defer until after Phase 5c.
- **Phase 4 (FD reparam) in isolation**: P4_PLAN.md notes this needs `PiecewiseC1PathOn.concat` as a prerequisite. Do *not* attempt Phase 4 before Phase 5a.
- **Re-architecting `OnCurvePV/`**: the three files there are well-factored already; golf only.
- **Sphere-packing endgame in `SpherePacking/`**: the planned use of `generalizedResidueTheorem` for the Viazovska contour is good but it lives in this repo as scaffolding. Once `Modularforms/` is split off too (Phase 1), this gets archived to a sibling repo. Re-merge only when the scoping decision is reversed.

### Fundamental obstacles

- **GRT *is* load-bearing for HW3.3.** It cannot be dropped wholesale even though it is large. (The orphaned subdirectories `WindingNumber/{CrossingAnalysis,Decomposition}` are exceptions.)
- **`MultiCrossingCPV.lean` is genuinely complex** (4,803 lines). The mathematics here — multi-pole CPV with sorted crossings and inductive convergence — is the "soul" of HW3.3. Realistic floor for this single file with aggressive golf: 2,500-3,000 lines.
- **The valence formula's per-elliptic-point case work** (`WindingWeights/{I,Rho,RhoPlusOne}.lean`, ~2,368 combined) reflects genuine mathematical content. Parametrisation collapses ~30% but not 70%.
- **No automation pipeline can do the proof-by-proof golf for you.** The 595 long proofs each need a human-or-LLM-in-the-loop pass. The recent waves show this is sustainable: 8 waves of "break up large proofs" landed across days, not weeks. But it does not happen in an afternoon.

---

## Part 6 — Comparison to sphere packing repo experience

The sphere packing repo (`~/Documents/GitHub/Sphere-Packing-Lean`, branch `cleanup-magic-function-a`) underwent a cleanup that took ~54k → 26,456 lines (-52%) over a sustained effort. Reference materials are `Sphere-Packing-Lean/PROJECT_OVERVIEW.md` (455 lines) and `Sphere-Packing-Lean/CLEANUP_PLAN.md` (405 lines).

### What worked in sphere packing

1. **Phase 1 was massive: ~1,200 lines deleted by dead-file removal** (15 dead files, identified by zero-importer grep). Direct analogue to Lever A here.
2. **Internal parameterisation of structural twins**: `SmoothJ24Common` parametrises J₂/J₄; sphere packing then *applied the same pattern* to J₁/J₅ → `J15Common` (estimated -120-150 lines). Direct analogue to Lever D's elliptic-point parametrisation.
3. **`fun_prop` annotation pass**: small qualitative changes that unlocked many downstream simplifications. Direct analogue to one corner of our Lever C.
4. **Mathlib-idiom alignment**: 15 audit findings each saving 5-25 lines individually, but totalling ~200 lines collectively and unlocking many downstream golf opportunities. Direct analogue to our Lever C.
5. **a/ vs b/ parallel module structure**: sphere packing has the analogous problem to our `WindingWeights/{I,Rho,RhoPlusOne}` triplet. The sphere packing repo solved this for I-side and J-side parameterisation. Direct analogue to Lever D Phase 3.

### What's different in this repo

- **Sphere packing started at 54k and got to 26k** (-52%). Their "drop subsystems" lever was much smaller because they had no orphan namespaces — everything was used by the main theorem.
- **This project's Lever A is uniquely large** because of how the Modularforms namespace ended up unused after the protected theorems were refactored to go through other infrastructure.
- **Sphere packing's per-file golf** averaged less than ours can. Their Priority-3 (generalisations) saves ~65 lines total; ours can save ~3,500 from the same kind of work *because we have so many more lines to start with*.
- **Both projects have 0 sorries in their main lines.** Sphere packing achieved this earlier; we have 10 sorries all in `Modularforms/`, all eliminated by Lever A.

### What the sphere packing experience suggests for our trajectory

| Sphere packing phase | LOC saved | Our analogue | Expected impact |
|---|---|---|---|
| Phase 1 dead-code | 1,200 | Phase 1 orphan drop | **14,120** (much larger) |
| Phase 2 naming + Phase 3 internal dedup | 520 | Phase 2 variant ratchet | **2,000** (larger) |
| Phase 4 parallel-module collapse (a/ vs b/) | ~2,000 | Phase 3 elliptic-point parametrisation | **1,500** (similar) |
| Mathlib-style golf | ~ subsumed | Phase 6 | **10,000+** (much larger) |

The 50% reduction the sphere packing repo achieved is the natural anchor. Our equivalent is **75k → 38k (-50%)**, which lands in the 35-45k range from Part 4's phased plan. That is consistent with what the levers honestly support.

**To get below 38k requires going further than sphere packing did** — and the cleanest way is Lever A (which sphere packing did not have available).

---

## Recommended execution sequence

In rough day-by-day terms, optimising for safety and momentum:

1. **Day 1**: Phase 1 (drop orphans). One commit per directory. -14,120 lines. Build & axiom-check.
2. **Days 2-7**: Phase 5a (`PiecewiseC1PathOn.concat`). Enabler for later phases.
3. **Days 8-21**: Phase 2 (variant ratchet collapse) + Phase 5b/c/d (API redesign). Run in parallel; they touch mostly distinct files.
4. **Days 22-42**: Phase 6 (mass golf via `/cleanup-all` orchestration). The workhorse.
5. **Days 43-56**: Phase 3 (elliptic-point parametrisation) + Phase 4 (FD reparam, now unblocked by Phase 5a).
6. **In parallel (calendar)**: Phase 7 (6 mathlib PRs).

After Day 56 the project should land in the 35-45k range. If the user genuinely wants to drive lower, a Phase 8 of "scope down to the minimal-version GRT" can take another 5-10k off but at the cost of generality.

---

## Verification protocol (every phase)

After each phase commit, before pushing:

```
lake build LeanModularForms 2>&1 | tail -3
# Must end with: Build completed successfully
```

Then `lean_verify`:
- `ForMathlib.valence_formula_textbook` → axioms `[propext, Classical.choice, Quot.sound]`
- `ForMathlib.hw_3_3_clean_full_mero` → same
- All 8 `hw_3_3_clean*` variants → same

Optionally snapshot the byte signatures of `valence_formula_textbook` and `hw_3_3_clean_full_mero` to a comment at the top of each file before starting a phase; verify byte-equal after the phase lands.

---

## Appendices

### A. The orphan list (Lever A, Phase 1) — exact files to remove

(50 files, 14,314 lines; see Part 2.2 for sizes.)

```
LeanModularForms/Modularforms/*.lean         (40 files, 11,542 lines — entire namespace)
LeanModularForms/SpherePacking/*.lean         (3 files, 1,281 lines — entire namespace)
LeanModularForms/ForMathlib/GeneralizedResidueTheory/WindingNumber/CrossingAnalysis.lean  (937)
LeanModularForms/ForMathlib/GeneralizedResidueTheory/WindingNumber/Decomposition.lean    (222)
LeanModularForms/ForMathlib/UpperHalfPlane.lean                                          (15)
LeanModularForms/ForMathlib/FunctionsBoundedAtInfty.lean                                 (13)
LeanModularForms/ForMathlib/SlashActions.lean                                            (39)
LeanModularForms/ForMathlib/CongruenceSubgrps.lean                                       (71)
```

### B. Variant clusters to collapse (Lever D, Phase 2)

- `residueTheorem_crossing_*`: 16 visible variants in `Crossing.lean`. Promote 2 canonical, alias 14.
- `hw_3_3_clean*`: 8 variants in `HW33Clean.lean`. Promote 1, alias 7.
- `dixonFunction_eq_zero*`: 12 variants in `DixonTheorem.lean`. Promote 1, alias 11.

### C. HW33 fan-out files to merge (Lever D, Phase 2)

Current 10 files (3,421 lines combined) → target 3 files (~2,000 lines):
- `HW33Paper.lean` (canonical statement + 1-line aliases)
- `HW33Multi.lean` (multi-pole consolidation)
- `HW33HigherOrder.lean` (higher-order branch)

### D. Long-proof hotlist (Lever C, Phase 6 first batch)

The 10 longest proofs to attack first (each ~50% golf target = ~150 saved per proof = 1,500 saved):

```
528  MultiCrossingCPV.lean:1281  perCrossing_higherOrder_window_integral_tendsto
484  MultiCrossingCPV.lean:2810  perCrossing_higherOrder_window_integral_tendsto_corner
361  MultiCrossingCPV.lean:1809  cpv_higherOrder_tendsto_along_sorted
360  MultiCrossingCPV.lean:2450  cpv_higherOrder_tendsto_along_sorted_corner
337  CrossingDataBuilder.lean:680  exists_left_cutoff
309  MultiCrossingCPV.lean:3333  hasCauchyPVOn_multiCrossing_higherOrder_corner
308  MultiCrossingCPV.lean:133   cpv_tendsto_along_sorted
298  ValenceFormula/WindingWeights/I.lean:347  ftc_logDeriv_telescope_i
280  MultiCrossingCPV.lean:2170  hasCauchyPVOn_multiCrossing_higherOrder
272  LocalCutoffs.lean:979       perCrossing_window_integral_tendsto_exact
```

### E. Final shipping target

If we execute Phases 1-6 to the optimistic end:
- 75,022 → 40-45k (-40%)
- 9 protected theorems still axiom-clean
- 0 sorries (down from 10, all eliminated by Phase 1)
- ~150 files (down from 210)
- All 8 `hw_3_3_clean*` variants and `valence_formula_textbook` still byte-signature-stable

If we execute Phase 7 (long calendar) and an aggressive Phase 8 (scope-down GRT generality):
- → 25-30k (-60% to -67%)

The stated 20k target should be treated as aspirational. A more honest milestone:
- **Q3 2026: 45k achieved.**
- **Q4 2026: 30k achieved.**
- **20k: only if the project decides to give up some generality.**

---

*End of CONSOLIDATION_PLAN.md.*
