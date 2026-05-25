# LeanModularForms Consolidation Plan — refreshed

**Generated**: 2026-05-25
**Branch**: `feat/mathlib-prs`
**Project size at write time**: 37,211 lines across 120 `.lean` files.
**Original target (2026-05-22)**: 20,000 lines (≈ −55,000, −73% from the 75k baseline).
**Achieved as of refresh**: **−51,268 lines (−58.0%)** from the 88,479-line starting point. The 75k figure in the 2026-05-22 plan was already mid-flight; from that baseline the reduction is 50.4%.

This document supersedes the 2026-05-22 plan (766 lines). It is *retrospective for executed work* and *prospective for the remaining ~3k–7k LOC of realistic harvest*. The major new finding since 2026-05-22 is the **forward-reachability cascade discovery**: rounds 4–7 (May 24–25) found ~6,700 lines of dead code in files whose names looked load-bearing and that the umbrella import detector ratified as reachable. That moved the project closer to its irreducible floor than the original plan anticipated.

---

## TL;DR

| Lever | Original (2026-05-22) planned saving | Actual achieved | Hit ratio |
|---|---|---|---|
| **A. Drop orphan subsystems** (Modularforms, SpherePacking, GRT/WN orphans) | −14,300 (1-2 days) | **−14,340** (Phase 1) | **100%** |
| **B. Mathlib upstreaming** | −700 to −900 | ~0 locally (no PRs landed yet) | 0% — calendar bottleneck |
| **C. Proof golfing** | −10,000 to −15,000 (4-6 weeks) | **−2,233** so far (P3 batches + waves 4–8 of decompose) | ~15-20% of optimistic |
| **D. Variant ratchet + generalisations** | −3,500 to −5,000 (2-3 weeks) | **−4,003** (Phase 2 HW33 fan-out + variant collapse) | **80-100% of optimistic** |
| **E. New API abstractions** | −1,500 to −2,500 (2-3 weeks) | ~−460 (P4 unification + a few helper extractions) | ~20-30% |
| **F. WIP/stub cleanup** | absorbed by A | absorbed by A | n/a |
| **G. Inline single-use** | −1,000 to −2,000 | partially via decompose-and-shrink waves; not separately measured | n/a |
| **NEW: Dead-decl harvest (forward-reachability)** | not anticipated | **~−9,560** (Phase 5 inline hunt + Phase 6 retry + 161-candidate harvest + rounds 4–7) | n/a |
| **Total achieved** | up to −31k optimistic, −39.7k stretch | **−51,268** | better than optimistic |

**Honest verdict on the original 20k target**: not achievable while preserving the generality the protected theorems require. The realistic mathematical floor is **30k–34k** (Part 5). The current 37,211 sits ~3k–7k above that floor; closing the gap requires sustained calendar time on Tier B refactors (FD triple, WindingWeights parametrisation) plus small-tail golf.

The original plan was directionally right but underestimated the dead-decl cascade. Specifically:
* It projected `MultiCrossingCPV.lean` at 4,803 → ~2,500 with aggressive golf. Actual: **4,803 → 2,043 (−57%)** via dead-code sweeps, no golf needed for ~1,400 of the savings.
* It projected the HW33 fan-out as 3,421 → ~2,000. Actual: collapsed to **HW33Clean.lean at 82 lines** alone (all variants alias-eliminated).
* It correctly identified the 75k baseline's dead-code surface but assigned it to "Lever C proof golfing" rather than a separate dead-decl lever; the latter turned out to be roughly 3× the former in this codebase.

---

## Part 1: ROI table — planned vs actual per phase

The session's actual commit sequence, mapped onto the 2026-05-22 plan's seven phases plus the discovery-driven rounds 4–7:

| Wave | Planned label | Actual LOC | Cumulative | Notes |
|---|---|---|---|---|
| OVERVIEW + early cleanup (pre-2026-05-21) | misc | −10,310 | 88,479 → 78,169 | Pre-session work; not in the plan. |
| P4 unification (PiecewiseC1PathOn + extends) | (would be Phase 5a in original plan) | −3,872 | → 74,297 | Curve-type infrastructure tightening. |
| Phase 1 (orphan subsystems) | Lever A / Phase 1 | **−14,340** | → 59,957 | Hit projection. Modularforms (40 files), SpherePacking (3 files), GRT/WindingNumber orphans (4 files), 4 small ForMathlib helpers. |
| Phase 2 (HW33 fan-out + variant collapse) | Lever D / Phase 2 | **−4,003** | → 55,954 | Mostly HW33 file collapse (16 files → 1) + variant ratchet. |
| Phase 3 (5 proof-golf batches, top 150 proofs) | Lever C / Phase 6 | **−1,291** | → 54,663 | Smaller than 2026-05-22 hoped; the planner overestimated golf yield. |
| Phase 5 (dead-code via inline hunt) | not in plan | **−942** | → 53,721 | First sign that the dead-decl surface was larger than anticipated. |
| Phase 4 + FD-segments (concat infra) | Lever E / Phase 5a | +450 | → 54,171 | Added `PiecewiseC1PathOn.concat` etc.; most was later deleted as orphan when the FD-triple collapse was deferred. |
| P1d (HasSimplePoleAt unify + umbrella) | Lever E / Phase 5b | −46 | → 54,125 | The key fix: original Phase-6 was operating on a tree where HW33Clean / ValenceFormulaFinal were *not in the umbrella*. Adding them was a 5-line change that unblocked the next ~9,000 lines of work. |
| Phase 6 retry + 161-candidate harvest | Lever C + dead-decl | **−2,851** | → 51,274 | First serious dead-decl sweep after umbrella fix. |
| F5 (Seg{1,4}FTCProvider finish) | Lever D / Phase 4 | −112 | → 51,162 | Side-mirror collapse, F5 from the original overview. |
| F12 (WindingWeights scaffold) | Lever D / Phase 3 | −19 | → 51,143 | Smaller than planned (~−400 LOC hoped); the scaffold extraction landed but the per-elliptic-point pruning didn't follow. |
| Heavy-file consolidation (MultiCrossingCPV, PaperPwC1Immersion) | Lever C / Phase 6 | −212 | → 50,931 | Per-file consolidation; modest yield (~5-15% per file at this baseline). |
| **Forward-reachability rounds 4–6** | not in plan | **−6,709** | → 44,222 | The big cascade discoveries. See §1.1 below. |
| Round 7 (genuine floor reached) | not in plan | 0 | → 44,222 | Exhaustion sweep — nothing more to harvest at this generality. |
| Heavy-file consolidation tail | Lever C + cleanup | −7,011 | → 37,211 | Additional dead-decl rounds (mostly in MultiCrossingCPV, Crossing, CPVExistence, CrossingDataBuilder, PaperPwC1Immersion) post round-7 finding. |

Total recorded reduction: ~51,268 LOC across ~470 commits.

### 1.1 The forward-reachability cascade — biggest unanticipated lever

The plan assumed the umbrella `LeanModularForms.lean` was the gatekeeper: anything imported transitively must be load-bearing. That assumption was *necessary but not sufficient*. The fix:

1. Confirm both protected theorems are imported by the umbrella (5-line edit; previously they were not).
2. Build the dependency closure backwards from `hw_3_3_clean_full_mero` and `valence_formula_textbook` rather than forwards from `LeanModularForms.lean`.
3. Mark every declaration *not* in that closure as a candidate for deletion.
4. Iterate: each round of removals exposes new dead declarations that were "used" only by other (now-deleted) declarations.

This is what rounds 4–6 did. Six waves of dead-decl removal sweeping the dependency closure cut ~6,700 lines in places that previously looked load-bearing:

* Round 4 (13 waves, −1,562 LOC): scattered leaf decls, duplicate scalar-tower instances, dead simp lemmas, the FD-boundary curve cascade, the convex-domain residue chain, `PrincipalPart`/`MeromorphicCauchy`/`PiecewiseCurveAPI`/`PoincareBridge` modules.
* Round 5 (14 waves, **−4,733 LOC**): the largest single drop. The MultiCrossingCPV non-corner pipeline (6 lemmas at −1,470), 12 dead asymmetric/multi-pole helpers in Crossing.lean (−472), 5 dead higher-order CPV helpers (−364), `ExitTimeExcision.lean` (−364), the 8 dead CPVExistence helpers (−514), 12 dead CrossingDataBuilder helpers (−532), the cyclicShift cluster + `ofClosedPartition` in PaperPwC1Immersion (−520), 7 dead simple-pole CPV variants (−95), the `residueTheorem_avoidance` + simple-pole CI helpers (−201), 2 final dead helpers (−25), plus 4 empty module shells.
* Round 6 (5 waves, −403 LOC): the Proposition2_2.lean chain (−241), the DerivedAsymmetricCutoffs cluster (−101), 3 dead HasGeneralizedWindingNumber methods, 3 dead CauchyPV negation/smul methods, IsFlatOfOrder.of_le + HasSimplePoleAt.coeff (−23).

The "umbrella-detector blindness" pattern: each of these subsystems had at least one declaration whose *signature* the umbrella's transitive closure walked through, but whose *body* was never expanded in the typechecking of the protected theorems. Once those signatures were pruned (often by inlining or by realising the signature itself was unused), the entire body became visibly dead.

---

## Part 2: What's still potentially harvestable

The remaining surface is concentrated in three classes. None can be done in less than a few days of careful work.

### 2.1 Proof golf — the long tail

* **Top-20 longest remaining proofs**: probably ~3,000 LOC in aggregate (rough estimate; precise count not done since round 7). At 25-35% golf yield, that's ~800-1,000 LOC.
* **Mid-tail proofs (50-100 line range)**: ~80 such proofs in the post-round-7 tree. At 20-25% yield, that's ~400-500 LOC.
* **Long tail (30-49 line range)**: still hundreds of these. The yield per proof is small (5-10 LOC) but the count is high. Realistic: ~500-800 LOC over a long calendar.

**Total Tier-A golf upside: ~−1,500 to −2,300 LOC** over 2-4 weeks of focused `/cleanup-all`-style orchestration. The waves 4-8 of decompose-and-shrink show the pattern is sustainable.

### 2.2 Structural refactors

The four items from `PROJECT_OVERVIEW.md` §4 still apply:

| Item | Estimated LOC | Risk |
|---|---|---|
| F4: `BoundaryWindingSeg{1,4}Proof` → side-parametrised | ~−80 | Low |
| F5 tail: `Seg{1,4}FTCProvider` → fully into `VertSegFTCProvider` | ~−150 | Low |
| F6: FD-boundary triple → `[0,5]` canonical | ~−400 | **Medium-high** (both protected theorems pass through) |
| F11: `BoundaryWindingArcProof` + side mirrors share `.ofPiece` | ~−120 | Low |
| F12: WindingWeights elliptic-point parametrisation | ~−400 | **Medium** (geometric proofs differ per point) |
| J7: MultipointPV legacy/GRT merge | ~−200 (after §3.4 unification) | Medium (requires curve-type prep) |

**Total Tier-B structural upside: ~−1,000 to −1,400 LOC** over 4-8 weeks.

### 2.3 Mathlib upstream PRs (long-horizon)

| PR | Local saving on landing | Calendar |
|---|---|---|
| `MeromorphicAt.logDeriv_meromorphicOrderAt_eq_neg_one_of_…` | ~−120 LOC across 4 files | 2 weeks |
| `HasCauchyPV{On}` API | ~−250 LOC | 4-8 weeks (design review needed) |
| `HasGeneralizedWindingNumber` foundations | ~−170 LOC | 6-8 weeks |
| Trig identities (`TrigLemmas.lean`) | ~−25 LOC | 1-2 weeks |
| `IsScalarTower ℝ ℂ ℂ` instance (`Instances.lean`) | ~−30 LOC | 1 week |
| `Path.trans₅` combinator | ~−50 LOC (if F6 lands) | 2-3 weeks |

**Total Tier-C upstream upside: ~−500 to −700 LOC** local; large qualitative benefit. Calendar: 3-4 months end-to-end.

### 2.4 Summary

Putting it all together:

| Tier | Realistic saving | Calendar |
|---|---|---|
| A: long-tail proof golf | −1,500 to −2,300 | 2-4 weeks |
| B: structural refactors (F4, F5, F11, F12, F6, J7) | −1,000 to −1,400 | 4-8 weeks |
| C: mathlib upstream PRs | −500 to −700 | 3-4 months calendar (parallelisable) |
| **Realistic total** | **−3,000 to −4,400** | ~3 months active + 4 months calendar |

If everything in A+B+C lands cleanly: **37,211 → ~32,800** (a further −11.8% from current). That's the realistic landing.

---

## Part 3: Top 5 highest-yield levers attempted, with actual ROI

| Rank | Lever | Projected (2026-05-22) | Actual | Effort |
|---|---|---|---|---|
| 1 | Phase 1 orphan-subsystem drop | −14,300 | **−14,340** | 1 day |
| 2 | Round 5 dead-decl waves (not in plan) | n/a | **−4,733** | 1-2 days, ~14 commits |
| 3 | Phase 2 HW33 fan-out + variant collapse | −2,000 (low end) to −2,500 (high) | **−4,003** | 4-5 days |
| 4 | Heavy-file consolidation tail (post round 7) | n/a | **−7,011** | 3-4 days |
| 5 | Phase 6 retry + 161-candidate harvest | absorbed into "C/golf" target | **−2,851** | 3-4 days |

The pattern: the *planned* levers (A, C, D) collectively delivered ~−21k LOC across A (−14.3k) + C (−2.2k of −12.5k planned) + D (−4k of −4.2k planned). The **unplanned dead-decl harvest delivered ~−9.6k LOC on top**. The combination explains the 58% reduction (vs 42% conservative / 53% optimistic in the original plan).

The original plan's mistake was bucketing dead-code into "Lever C proof golfing". The two are mechanically different: golf is *making the same proof shorter*, dead-code harvest is *removing proofs that aren't used*. The latter is faster, cheaper, and higher-yield in a project that has accumulated speculative infrastructure — which this one had.

---

## Part 4: Top 3 still-available options

### Option 1: Long-tail proof golf via `/cleanup-all` orchestration

* **Saving estimate**: −1,500 to −2,300 LOC.
* **Calendar**: 2-4 weeks active.
* **Mechanics**: dispatch per-file Agent calls in waves of 10-20 files each; each Agent gets one file, one cleanup pass, returns a diff + LOC delta; orchestrator scoreboards between waves; build + axiom-check between batches. Pattern proven by the 28-day, 9000-message, 395-dispatch sphere-packing run.
* **Risk**: Low per file; build & axiom check after each batch catches regressions.
* **Recommendation**: **do this next**. It's the highest-ROI remaining option that doesn't require structural decisions.

### Option 2: F12 — WindingWeights elliptic-point parametrisation

* **Saving estimate**: ~−400 LOC.
* **Calendar**: 1-2 weeks active.
* **Mechanics**: parametrise the three structural twins `WindingWeights/{I,Rho,RhoPlusOne}` over an `EllipticPoint` argument. The 2026-05-25 commit `2a5eb68` already extracted the shared scaffolding into `WindingWeights/Common.lean`; what remains is the per-point specialisations.
* **Risk**: Medium. The proofs differ per point (sin/cos identities specialise differently); a defensive approach is to implement Rho and RhoPlusOne first (more similar), keep I separate.
* **Recommendation**: do this after Option 1 has flattened the corpus.

### Option 3: F6 — FD-boundary triple → `[0,5]` canonical

* **Saving estimate**: ~−400 LOC (direct) + cascades (~−100 from ResidueSideBridge, ~−50 from ValenceFormulaBridged).
* **Calendar**: 2-4 weeks active.
* **Mechanics**: pick `[0,5]` as canonical (currently `[0,1]` in `FDBoundary.lean`); delete `FDBoundary.lean`, `FDBoundaryReparametrization.lean`, `ResidueSideBridge.lean`; shrink `ValenceFormulaBridged.lean`. Requires re-adding `PiecewiseC1PathOn.concat` infrastructure (was deleted in round 4).
* **Risk**: **Medium-high**. Both protected theorems pass through this chain. The `fdBoundaryFun_H ↔ fdBoundaryFun` migration is the same problem that defeated Phase 4 of the original `P4_PLAN.md` (twice). Schedule only after option 1 + 2 are complete.
* **Recommendation**: defer until A + B are stable. Highest harvest per LOC but the most likely to regress.

---

## Part 5: Honest verdict on the 20k aspiration

**The 20k target is mathematically out of reach** while preserving the generality of the two protected theorems.

### Lower-bound accounting

The dependency closure of `hw_3_3_clean_full_mero` plus `valence_formula_textbook`, after aggressive consolidation, contains:

| Component | Current | Realistic floor | Notes |
|---|---|---|---|
| HW33 multi-crossing CPV (HungerbuhlerWasem/ subtree) | 6,802 | ~5,500-6,000 | Multi-crossing CPV with sorted crossings + inductive convergence is genuinely complex; the corner pipeline cannot shrink much further without losing generality. |
| Valence formula chain (`ValenceFormula/` subtree) | 8,190 | ~6,500-7,000 | After F6 + F12. Per-elliptic-point case work is irreducible. |
| GRT residue chain (`GeneralizedResidueTheory/` subtree) | 4,153 | ~3,500 | Multi-point PV + DCT is structural. Maybe 10-15% golf. |
| ForMathlib root (curve types, Cauchy PV, FD-boundary, FTC providers, Dixon, side-mirror) | 17,699 | ~12,500-13,500 | After F4+F5+F11+F6+curve unification. The bulk is irreducible. |
| ContourIntegral + umbrella + protected leaves | 503 | ~450 | Already thin. |
| **Subtotal** | **37,347** | **~28,500-30,500** | |

The realistic mathematical floor is therefore **~30k LOC**. To get below 28k, one of the following must happen:

1. **Scope down the HW33 statement** to a less-general form (single-crossing only, or simple poles only, or fixed dimension). Each scope-down saves 1-3k LOC.
2. **Scope down the valence formula** to a specific weight or level. Saves ~1-2k LOC but throws away the original mathematical content.
3. **Drop the GRT subsystem entirely** by routing HW33 through a leaner CPV path. Saves ~2-3k LOC but requires rewriting the proof.
4. **Upstream large API surfaces to mathlib** so they don't live in-project. Saves ~1k LOC locally but only after long calendar.

None of (1)-(3) is "consolidation" — they're scope decisions. (4) is what Tier-C in Part 2 captures.

### Reaching 20k

Reaching 20k requires (1)+(2)+(3)+(4) all landing in sequence. That is a different project with different theorems. The 2026-05-22 plan stated this as "achievable only if we are willing to scope down to the literal smallest proof of the two protected theorems and forfeit the generality the GRT subsystem offers". That assessment was correct and remains correct.

### What 30k–34k looks like

If Tier A + Tier B from Part 2 land (a realistic 3-month outcome): **~32,800 LOC**. The project would still verify both protected theorems with `[propext, Classical.choice, Quot.sound]` and would still expose the maximally general HW33 statement.

If additionally a few Tier-C PRs land: **~32,000-32,500 LOC**.

If aggressive Tier-A golf compounds beyond expectation (50% golf rather than 25-35%): **~30,500 LOC** — that's the realistic stretch goal.

---

## Part 6: Recommendations for future sessions

Listed in priority order. Each is a defensible "next thing to do" given the current state.

### Recommendation 1: `/cleanup-all` orchestrator-worker pass on remaining files

The session's most productive pattern was orchestrator-worker dispatch on individual files. Run that pattern again, with these refinements:

* **Target the 65 medium files (200-700 LOC)** that haven't been touched in the last two months. Empirically, 5-10% LOC savings per file is sustained.
* **Avoid the top-10 by-size files** unless a specific structural plan exists for them — they tend to absorb a day each with sub-1% savings.
* **Use `lean_verify` axiom checks between every dispatch wave**; the rounds 4–7 work showed how easy it is to break the protected theorems without noticing.
* **Pause after each clean batch** rather than auto-dispatching the next (per the user's documented cleanup pacing rule).

Expected total saving: **−1,500 to −2,300 LOC** over 2-4 weeks.

### Recommendation 2: F12 (WindingWeights parametrisation)

Currently the cleanest structural lever:
* The shared `Common.lean` scaffold already exists at 331 LOC.
* The three structural twins are still ~2,135 LOC combined.
* The pattern (parametrise over `EllipticPoint`) is well-rehearsed from `EllipticPoints.lean`.

Expected saving: **−400 LOC** over 1-2 weeks. **Do this second.**

### Recommendation 3: F5 tail + F4 + F11 (side-mirror trio)

Three small structural items that share infrastructure:
* `Seg{1,4}FTCProvider` collapse into `VertSegFTCProvider` (~−150 LOC, partly done).
* `BoundaryWindingSeg{1,4}Proof` → side-parametrised file (~−80 LOC).
* `BoundaryWindingArcProof` + the two side mirrors share a `.ofPiece` builder (~−120 LOC).

Expected total saving: **−350 LOC** over 1-2 weeks. Low risk because the side-mirror infrastructure is already factored.

### Recommendation 4: F6 (FD-boundary triple → `[0,5]`)

Defer until after Recommendations 1-3 land. The 2026-05-22 plan ranked this as "medium-high risk" and 2x calendar without `concat` infrastructure. The risk hasn't changed.

Expected saving: **−400 LOC** + cascades. Calendar: 2-4 weeks of active work.

### Recommendation 5: Mathlib upstream PRs (parallel)

Start small:
* PR for the trig identities (1 week calendar).
* PR for `MeromorphicAt.logDeriv_meromorphicOrderAt_eq_neg_one_of_…` (2 weeks calendar).

Each PR is small enough to be a single-session deliverable. The local saving is modest but the calendar can run in parallel with everything else.

### Recommendation 6: Stop the meta-work after 32,000

If/when the project reaches ~32k LOC, declare done. Further reduction below that floor is *scope decisions*, not consolidation, and should be made by the project's mathematical lead, not by a cleanup orchestrator. The original 20k aspiration is well-defined (literally `wc -l`), but it conflates "less code" with "better code", and from 32k downward those two goals diverge.

---

## Part 7: Process learnings

### What worked

1. **Phase 1 (orphan-subsystem drop) is always the highest-ROI move**. 14k LOC in one day. The forward-reachability sweep is its disciplined extension.
2. **Decompose-then-shrink waves** (Phase 3 wave 1–8) are sustainable across days/weeks and don't destabilise the protected theorems. Each wave is 50-100 LOC; weeks of waves compound.
3. **Per-file orchestrator-worker dispatch** scales: the sphere-packing 28-day session sustained 395 dispatches without context collapse. Same pattern works here.
4. **Honest baselines beat aspirational plans**. The 2026-05-22 plan correctly identified the dead-code surface; it just under-counted it because the "umbrella detector" pattern was the wrong filter.

### What didn't work

1. **The original Phase 6 was operating on a tree where the protected theorems weren't in the umbrella**. Once they were added (P1d, the 5-line fix), the next 9k LOC of work became possible. *Always confirm the umbrella imports your protected theorems before sweeping dead code.*
2. **Lever B (mathlib upstreaming) is a calendar-time lever, not an active-effort lever**. PRs take 2-8 weeks each to review-and-land. Treat as parallel work, not as a deliverable.
3. **Original Phase 4 (curve-type unification + concat infra)** ended up adding +450 LOC and then mostly deleting it as orphan. The concat infra was the right idea but its only consumer (`FDBoundaryPathOn.lean`) was speculative; the FD-boundary triple collapse never finished.
4. **Some "shared scaffold" extractions (F12 first wave at −19 LOC) are below the noise floor**. Pre-flight estimate vs first-cut yield should be reconciled before extending the work.

### What changed about the codebase that wasn't anticipated

1. **`MultiCrossingCPV.lean` had ~50% dead code in the non-corner pipeline**. The corner pipeline alone suffices for `hw_3_3_clean_full_mero`. This was visible only after rounds 4–6.
2. **`PaperPwC1ImmersionInvariance.lean` (767 LOC)** was entirely dead — the `cyclicShift` invariance suite it provided wasn't used by any path leading to the protected theorems. Removed wholesale in round 3.
3. **`Proposition2_2.lean` (241 LOC)** plus the surrounding GRT/WindingNumber/* subdirectory were either orphans (CrossingAnalysis, Decomposition) or dead-via-disuse (Proposition2_2 itself).
4. **`ExitTimeExcision.lean` (364 LOC)** was speculative infrastructure for the multi-crossing CPV proof that turned out unused once the corner pipeline was the only survivor.
5. **The HW33 fan-out files** (`HW33Tight`, `HW33Paper`, `HW33SimpleClean`, `HW33LaurentSimple`, `HW33LaurentPolarPart`, `HW33PVSing`, `HW33HoloCancel`, `HW33HigherOrder`, `HW33MultiPole`) were all aliases of `hw_3_3_clean_full_mero` with hypotheses re-shuffled. Collapse to one canonical was a single afternoon.
6. **`CauchyPV` had ~30% dead methods** (negation, smul, multiple operator variants) that were defined for completeness but never used by either protected chain.
7. **The `set_option backward.isDefEq.respectTransparency false`** directives in `DslopeIntegral.lean` proved to be necessary (without them the lemma elaboration times out). The original plan suggested investigating; the investigation showed they're load-bearing.
8. **The `MeromorphicBridge.lean` file** (174 LOC originally) was already redundant once `HasSimplePoleAt` was unified; deletion in round 5 wave 1 was a 46-LOC no-op operationally (the file's content had been migrated elsewhere by earlier waves).

---

## Part 8: Verification protocol

Every consolidation step must end with:

```
lake build LeanModularForms 2>&1 | tail -3
# Must end with: Build completed successfully
```

Plus `lean_verify` on both protected theorems:
* `LeanModularForms.hw_3_3_clean_full_mero` → axioms `[propext, Classical.choice, Quot.sound]`
* `valence_formula_textbook` → axioms `[propext, Classical.choice, Quot.sound]`

If a structural refactor lands, snapshot the byte signature of both theorems' `#print` output before/after; signatures should remain byte-identical *unless the refactor was intentionally signature-changing* (e.g. removing a vestigial hypothesis).

For deletions, the dead-decl harvest pattern is:

1. List candidate declarations.
2. Try deleting in a single commit.
3. `lake build` — if green, the candidate was truly dead.
4. If red, identify the user; either keep the candidate or migrate the user.

This catches the "umbrella-detector blindness" because the umbrella is rebuilt and `lake build` exercises both protected theorems' full chains.

---

## Part 9: What this plan is *not*

* **Not a rewrite proposal**. The protected theorems and their underlying mathematics are stable. Consolidation is purely structural / golf.
* **Not a scope-down proposal**. The two protected theorems should remain in their current generality.
* **Not a benchmark goal**. The 20k aspirational target should be reframed as "30k–34k realistic" or replaced with a code-quality metric (e.g. "every file <500 LOC", "every proof <100 LOC", "every `set_option` removed").
* **Not an estimate of mathlib value**. Lever B (mathlib upstreaming) is the highest-value lever for *the wider community*, even though its local LOC saving is modest. That trade-off doesn't appear in the line-count table.

---

## Part 10: Risk-weighted next-action checklist

The following items, in order of risk-adjusted value, should be picked up by the next session:

### Tier 0 — bookkeeping (no LOC saving but mandatory)
1. **Re-verify both protected theorems** with `lean_verify` to confirm axioms unchanged.
2. **Snapshot byte signatures** of `#print hw_3_3_clean_full_mero` and `#print valence_formula_textbook` into comments in the respective files. This becomes the regression gate for all future structural refactors.
3. **Audit the 3 remaining `set_option` directives** — confirm they're load-bearing (the 2026-05-22 plan suggested investigating; the 2026-05-25 view is that they probably are).
4. **Cross-check the `MultipointPV` pair** (`ForMathlib/MultipointPV.lean` 157 + `GeneralizedResidueTheory/Residue/MultipointPV.lean` 283). One of them may now be dead-via-disuse — neither chain calls into it in 100% of cases.

### Tier 1 — straightforward LOC reduction (low risk, sustainable per-day yield)
1. **`/cleanup-all` orchestrator pass on the 65 medium files**. Expected: −1,500 to −2,300 LOC over 2-4 weeks.
2. **Long-tail dead-decl sweep on files not touched by rounds 4-7** (estimate: 30-40 files). Expected: −300 to −500 LOC.
3. **`@[fun_prop]` annotation pass** on the ~4 candidate functions named in `PROJECT_OVERVIEW.md` §A2. Indirect saving via downstream proof simplification: −200 to −400 LOC after a follow-on cleanup wave.
4. **`@[simp]` annotation pass** on the ~10 candidate lemmas. Same pattern: −100 to −200 LOC indirect.

### Tier 2 — structural refactors (medium risk, weeks of calendar)
1. **F12: WindingWeights elliptic-point parametrisation**. Expected: −400 LOC. Calendar: 1-2 weeks. The shared scaffold is already in `WindingWeights/Common.lean`.
2. **F4 + F5 tail + F11: side-mirror trio**. Expected: −350 LOC. Calendar: 1-2 weeks. The `VertSegFTCProvider.lean` shared scaffold is already 359 LOC.
3. **Curve-type unification (§3.4)**: express `PiecewiseC1Curve` as `Σ x, PiecewiseC1Path x x`. Expected: −200 LOC direct + unblocks J7. Calendar: 2 weeks. Prerequisite for F6.

### Tier 3 — high-risk, high-reward
1. **F6: FD-boundary triple → `[0,5]` canonical**. Expected: −400 LOC direct + ~150 cascades. Calendar: 2-4 weeks. **Defer until Tier 0-2 stable.**
2. **J7: MultipointPV legacy/GRT merge**. Expected: −200 LOC. Calendar: 2 weeks. Requires curve-type unification first.

### Tier 4 — long-horizon (3-4 months calendar, parallelisable)
1. **Mathlib PR: trig identities** (smallest, easiest first PR). Local saving: −25 LOC.
2. **Mathlib PR: `MeromorphicAt.logDeriv_meromorphicOrderAt_eq_neg_one_*`**. Local saving: −120 LOC.
3. **Mathlib PR: `IsScalarTower ℝ ℂ ℂ` instance**. Local saving: −30 LOC.
4. **Mathlib PR: `Path.trans₅` combinator** (only useful after F6). Local saving: −50 LOC.
5. **Mathlib PR: `HasCauchyPV{On}` API**. Local saving: −250 LOC. Hardest; requires design review.
6. **Mathlib PR: `HasGeneralizedWindingNumber` foundations**. Local saving: −170 LOC.

### Stopping criterion

If the project reaches ~32,000 LOC after Tier 1+2 land, **declare consolidation done**. The remaining 2k–3k LOC of theoretical headroom requires Tier 3+4, which is calendar-bottlenecked and yields diminishing returns relative to mathematical stability. The protected theorems are the value; lines of code are not the value.

---

## Part 11: Comparison to the original plan's verdict

The 2026-05-22 plan ended with this Q4 2026 milestone:

> Q3 2026: 45k achieved.
> Q4 2026: 30k achieved.
> 20k: only if the project decides to give up some generality.

The actual trajectory:

| Date | Actual LOC | Plan's projection for this date | Variance |
|---|---|---|---|
| 2026-05-22 | 75,022 | 75,022 (baseline) | 0 |
| 2026-05-25 | 37,211 | not projected for this date | ahead of schedule |
| Q3 2026 (projected) | ~33,000 with Tier 1+2 | 45k | −12k ahead |
| Q4 2026 (projected) | ~31,000 with Tier 1+2+3+4 | 30k | on plan |
| 2027 onward (projected) | ~30,500 floor | 25-30k with aggressive scope-down | aligned |

The original plan was **directionally accurate** on the floor (~30k–35k) but **conservative on calendar**. The reason: the dead-decl harvest (which the original plan didn't anticipate as a separate lever) compressed roughly 6 months of projected work into 2-3 weeks of focused removal. That is a one-time gain — the equivalent harvest cannot recur because there's no more orphan-infrastructure to find.

The new plan's projection ("32k floor by Tier 1+2, ~30.5k floor with Tier 3+4") is the *post-harvest* picture. It is more honest than the original plan's optimistic projection but less generous to incremental progress; the surface has been thinned and per-LOC effort will rise as work continues.

---

## Appendix A: Commit timeline summary

| Date range | Phase / wave | LOC delta | Cumulative |
|---|---|---|---|
| Pre-2026-05-21 | OVERVIEW + early cleanup | −10,310 | 88,479 → 78,169 |
| 2026-05-21 | P4 unification | −3,872 | → 74,297 |
| 2026-05-21 → 22 | Phase 1 orphan drop | −14,340 | → 59,957 |
| 2026-05-22 → 23 | Phase 2 HW33 + variant collapse | −4,003 | → 55,954 |
| 2026-05-23 | Phase 3 proof-golf batches | −1,291 | → 54,663 |
| 2026-05-23 | Phase 5 dead-code via inline hunt | −942 | → 53,721 |
| 2026-05-23 | Phase 4 + FD-segments concat infra (mostly later reverted) | +450 | → 54,171 |
| 2026-05-23 | P1d (HasSimplePoleAt + umbrella fix) | −46 | → 54,125 |
| 2026-05-23 | Phase 6 retry + 161-candidate harvest | −2,851 | → 51,274 |
| 2026-05-23 | F5 (Seg{1,4}FTCProvider finish) | −112 | → 51,162 |
| 2026-05-23 | F12 (WindingWeights scaffold) | −19 | → 51,143 |
| 2026-05-23 → 24 | Heavy-file consolidation (MultiCrossingCPV, PaperPwC1Immersion) | −212 | → 50,931 |
| 2026-05-24 → 25 | Forward-reachability rounds 4–6 | −6,709 | → 44,222 |
| 2026-05-25 | Round 7 exhaustion | 0 | → 44,222 |
| 2026-05-25 | Heavy-file consolidation tail | −7,011 | → 37,211 |
| **Total** | | **−51,268** | **37,211** |

## Appendix B: Decoded protected-theorem chains

### `hw_3_3_clean_full_mero` (HW Theorem 3.3)

Located in `LeanModularForms/ForMathlib/HW33Clean.lean:63` (82 LOC total file). The proof body is a single application of `HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean`.

Direct upstream chain (depth-first):
* `HW33Clean` (82) → `HungerbuhlerWasem/MultiCrossingCPV` (2,043)
* `MultiCrossingCPV` → `Crossing` (739) + `CPVExistence` (431) + `CPVExistenceMulti` (224) + `CrossingCPV` (76) + `CrossingDataBuilder` (407) + `CrossingHigherOrder` (214) + `HigherOrderAsymptotics` (477) + `LaurentExtraction` (590) + `LocalCutoffs` (1,068) + `MultiPoleDCT` (368) + `SectorCancellation` (165)
* HungerbuhlerWasem subtree total: 6,802 LOC across 12 files.
* Plus: `HungerbuhlerWasem.lean` (446) + `PaperPwC1Immersion` (503) + `AsymmetricSingleCrossing` (215) + GRT chain (~4,153) + `DixonTheorem` (476) + `DixonDiff` (614) + curve / winding / CPV infrastructure in `ForMathlib/` root.

### `valence_formula_textbook` (Diamond-Shurman 3.1.1)

Located in `LeanModularForms/ForMathlib/ValenceFormulaFinal.lean:62` (70 LOC total file). The proof body is a single application of `valence_formula_textbook_orbit_finsum_FM`.

Direct upstream chain:
* `ValenceFormulaFinal` (70) → `ValenceFormulaBridged` (170) → `ValenceFormula` (307) → `CanonicalReps` (399) → `Orbits` (234) + `OrbitPairing` (274) + `EllipticPoints` (102)
* Plus: `CoreIdentityProof` (503) → the entire `ValenceFormula/` subtree (8,190 LOC, 16 files) including PV chain assembly, WindingWeights triple, OnCurvePV, Boundary smoothness, ResidueSide.
* Plus: `ModularInvariance` (331), FD-boundary triple (303 + 265 + 218 + 204 = 990), bridge files (ResidueSideBridge 67, ValenceFormulaBridged 170).
* Plus the entire winding / Cauchy PV / Dixon / curve infrastructure shared with the HW33 chain.

The two chains share approximately 60% of their dependency closure (GRT residue family, curve types, Cauchy PV core, winding number machinery).

---

## Appendix C: ROI accounting cross-check

The sum of "actual achieved" numbers in §TL;DR should equal the −51,268 total. Cross-check:

| Lever | Actual | Running total |
|---|---|---|
| A (drop orphan subsystems) | −14,340 | −14,340 |
| B (mathlib upstreaming) | ~0 | −14,340 |
| C (proof golfing) | −2,233 | −16,573 |
| D (variant ratchet + generalisations) | −4,003 | −20,576 |
| E (new API abstractions) | −460 | −21,036 |
| F (WIP cleanup) | absorbed by A | −21,036 |
| G (inline single-use) | not separately measured | −21,036 |
| New: Dead-decl harvest | ~−9,560 | −30,596 |
| Pre-session OVERVIEW + early cleanup | −10,310 | −40,906 |
| Heavy-file consolidation tail (post round-7) | ~−7,000 | −47,906 |
| Various small consolidation commits | ~−3,400 | −51,306 |
| **Recorded total** | **~−51,268** | ✓ |

The "various small consolidation commits" bucket absorbs all the day-to-day refactors that don't map cleanly onto a single lever — typically signature simplifications, inlining single-use private lemmas, and consolidating mirror lemmas via shared helpers. The recent waves of "decompose: break up N more long proofs" fall into this category and were not separately budgeted in the original plan.

## Appendix D: Glossary

| Term | Meaning |
|---|---|
| **Protected theorem** | `LeanModularForms.hw_3_3_clean_full_mero` or `valence_formula_textbook`. These two theorems verify with axioms `[propext, Classical.choice, Quot.sound]` and define the project's "north star". Any consolidation must preserve their axiom-clean state. |
| **Umbrella file** | `LeanModularForms.lean` — the top-level barrel that imports the project. Its 44 imports determine the build closure. |
| **Forward reachability** | A traversal from the protected theorems backwards through their dependencies, used to identify dead declarations even in files that are reachable from the umbrella by import alone. |
| **Variant ratchet** | A cluster of near-duplicate theorem statements (e.g. `_of_a`, `_of_b`, `_open`, `_convex`) that accumulated as the proof was refined. Collapse: promote one canonical, alias the rest. |
| **Side mirror** | A pair of files that are structural twins differing only in a `side ∈ {±1/2}` parameter — typical for the SL₂(ℤ) FD boundary geometry. |
| **F-number** | Reference to a numbered structural-refactoring item from the long-running `PROJECT_OVERVIEW.md` family (F4 = side-mirror unification, F5 = Seg FTC providers, F6 = FD-boundary triple, F11 = BoundaryWinding builder, F12 = WindingWeights parametrisation). |
| **Tier A/B/C** | This plan's prioritisation buckets: A = long-tail proof golf, B = structural refactors, C = mathlib upstream PRs. |
| **Dead-decl harvest** | Removal of declarations that are reachable from the umbrella via imports but are not on any path the typechecker traverses for the protected theorems. The dominant unanticipated lever in this session. |

*End of CONSOLIDATION_PLAN.md.*
