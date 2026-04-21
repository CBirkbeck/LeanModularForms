# Legacy Port Plan: Converting `ForMathlib/Legacy/` to New API

**Status:** Drafted 2026-04-20 after the consolidation that landed in commit `68c025a`.

**Goal:** Eliminate `LeanModularForms/ForMathlib/Legacy/` by re-expressing every theorem it contains in the new-API types (`PiecewiseC1Path`, `HasCauchyPV*`, `HasGeneralizedWindingNumber`, no `'`-suffixed CPV API). After this plan completes, every `ForMathlib/*.lean` file will be a mathlib-PR candidate using exclusively new API.

**Reference plan:** `docs/superpowers/plans/2026-04-07-mathlib-prs-v2.md` (the PR decomposition design). This plan refreshes it to match the **current** state: Chain 1 is essentially complete in pure ForMathlib, and the work that remains is specifically the Chain 2 (valence formula) proof and the "oracle closure" of Chain 1.

**Scale:** 60 Legacy files, ~25 000 lines, organized around three conceptual blocks.

---

## Where we are today

### Pure ForMathlib (82 files, all PR-ready style)

- **Foundation (7):** `PiecewiseC1Path`, `PiecewiseContourIntegral`, `CauchyPrincipalValue`, `GeneralizedWindingNumber`, `Residue`, `PoincareBridge`, `SingleCrossing`.
- **Chain 1 analytical (complete, PR candidates on their own):** `CurveUtilities`, `CrossingAnalysis`, `WindingDecomposition`, `WindingHomotopy`, `HomotopyDefs`, `PVSplitting`, `SegmentFTC`, `MultipointPV`, `SimplePoleIntegral`, `ResidueCircleIntegral`, `MeromorphicBridge`, `PrincipalPart`, `SectorCurve`, `FlatnessConditions`, `NullHomologous`, `DixonDef`, `DixonDiff`, `DixonTheorem`, `MeromorphicCauchy`, `Cycles`, `PoincareBridge`.
- **Chain 1 main theorem (incomplete — oracle form):** `GeneralizedResidueTheorem`, `HigherOrderAssembly`, `HigherOrderCancel`. These theorems take `hCancel`, `hPV_sing`, `hI_*` as hypotheses that **should** be derivable from `SatisfiesConditionA' ∧ SatisfiesConditionB`.
- **Valence-formula infrastructure (FM versions):** `EllipticPoints`, `ModularInvariance`, `Orbits`, `OrbitPairing`, `CanonicalReps`, `FDBoundary`, `FDBoundaryPath`, `FDWindingDataFullSeg1Seg4`, `FDWindingDataFullAssembly`, `SegmentAnalysis`, `LogDerivModularForm`, `InteriorContourIntegral`, `InteriorWinding`, `InteriorWindingProof`, `HorizontalContribution`, `ModularContourIntegral`, `ModularSideProof`, `ResidueSideProof`, `PVChainProof`, `SmoothBoundaryWindingProof`, `WindingWeightProofs`, `WindingWeightsUnconditional`, `BoundaryWinding`, `BoundaryWindingArcProof`, `BoundaryWindingSeg1Proof`, `BoundaryWindingSeg4Proof`, `CrossingAtI`, `CrossingAtRho`, `ArcFTC`, `ArcFTCAtI`, `ArcFTCLimit`, `ArcGenericFTCProvider`, `Seg1FTCProvider`, `Seg4FTCProvider`, `CornerFTCAtRho`, `FDBoundaryReparametrization` (sic — currently in Legacy, see below), `CoreIdentityProof`, `ValenceFormula`, `ValenceFormulaFinal`.
- **Top-level statements (clean, verify with only standard axioms):** `valence_formula_textbook`, `generalizedResidueTheorem`, `dixonFunction_eq_zero`.

### Legacy (60 files, ~25 000 lines, used only to supply valence-formula proof)

Current dependency of `ValenceFormulaFinal` enters Legacy via exactly one edge: `ForMathlib.ValenceFormulaFinal → Legacy.ValenceFormulaBridged`. The bridge then uses the rest of Legacy.

Legacy breakdown by mass:

| Subdir | Files | Lines | What's there |
|---|---|---|---|
| `GeneralizedResidueTheory/` | 25 | 13 121 | Old-API CPV/winding/residue/homotopy + PV infrastructure |
| `ValenceFormula/` | 19 | 10 787 | Orbit/pairing, boundary, winding weights at i/ρ/ρ+1, PV chain assembly |
| `ContourIntegral/` | 4 | 603 | PV split, crossing limit, segment FTC helpers |
| Bridge files | 6 | 1 109 | `ClassicalCPV`, `FDBoundaryH`, `FDBoundaryReparametrization`, `ResidueSide`, `ResidueSideBridge`, `ValenceFormulaBridged` |

---

## Guiding principles for the port

1. **Do not re-prove anything that pure ForMathlib already has.** When a Legacy theorem has a pure-FM analogue (usually with the `FM` suffix), the port replaces calls with the FM version; it does not duplicate the proof.
2. **Every week ends with a green build and a commit.** No WIP stays longer than a week.
3. **Prefer deletion over rewrite when the callers are all Legacy.** Most Legacy files only serve the Legacy chain; after downstream Legacy files are ported, the upstream ones die automatically.
4. **Use the new types strictly.** `PiecewiseC1Path` / `HasCauchyPV*` / `HasGeneralizedWindingNumber`. No `fdBoundary_H` on `[0,5]`, no `generalizedWindingNumber'`, no `cauchyPrincipalValue'` in the port targets.
5. **Bridges die last.** The last step is to delete `FDBoundaryH`, `ClassicalCPV`, `FDBoundaryReparametrization`, `ResidueSide`, `ResidueSideBridge`, `ValenceFormulaBridged` when nothing references them.

---

## KEY INSIGHT: the valence formula theorem is ALREADY in pure ForMathlib

The file `ForMathlib/ValenceFormulaBridged.lean` proves:

```lean
theorem valence_formula_textbook_orbit_finsum_FM :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbitFM), ordOrbitQFM f q = (k : ℂ) / 12
```

Every symbol in this statement is pure-FM. The theorem verifies with **0 custom
axioms** (only standard `propext`, `Classical.choice`, `Quot.sound`). It's
re-exported as `valence_formula_textbook` in `ValenceFormulaFinal.lean`.

**The valence formula has been proven** in a file that lives under
`LeanModularForms/ForMathlib/`. What remains (the Legacy subdirectory under
ForMathlib/) is implementation detail that supplies the analytic Tendsto proofs
used internally.

## Status audit (2026-04-21): most phases are already done

A careful audit of pure ForMathlib versus the Legacy chain reveals that **81 of 82
pure ForMathlib files are already fully Legacy-free** — their transitive import
closure stays entirely within `ForMathlib/` (non-`Legacy/`). Only
`ValenceFormulaFinal.lean` touches Legacy, via a single bridge edge to
`Legacy/ValenceFormulaBridged`.

Mapping to the phase structure below:

| Phase | Status | Notes |
|---|---|---|
| **0 Consolidation** | ✅ Done | Commit `7b0a76a` |
| **1 Close oracle** | ✅ Done for convex + avoidance | `hasCauchyPVOn_simplePoles_convex_auto` in `HigherOrderAssembly.lean` already derives hCancel / hPV_sing / integrability from simple-pole + convex-domain + avoidance. Crossing case = Phase 6. |
| **2 Port `fdBoundary`** | ⚠️ Partial | Pure FM has `fdBoundaryFun`, `fdBoundaryPath`, `FDWindingDataFull`. The bridges `FDBoundaryH` + `FDBoundaryReparametrization` exist in Legacy as legacy-implementation; they're only reachable from `ValenceFormulaFinal` via the bridged proof path. |
| **3 Winding weights** | ✅ Done | `WindingWeightsUnconditional.hasWindingNumber_at{I,Rho,RhoPlusOne}_of_scd` + instantiations via `ArcFTCAtI`, `CornerFTCAtRho`, `SingleCrossing`. All in pure FM. |
| **4 Interior winding** | ✅ Done | `InteriorWindingProof.lean` + `InteriorContourIntegral.lean` in pure FM. `fdBoundary_interior_winding_complete` wired into `fdWindingData_unconditional`. |
| **5 Modular side** | ✅ Done | `ModularInvariance`, `OrbitPairing`, `Orbits`, `ModularSideProof`, `HorizontalContribution`, `ModularContourIntegral` all in pure FM. |
| **6 PV chain assembly** | ❌ Not done (the one genuine blocker) | The CPV of `logDeriv f` in the **crossing** case (γ crosses zeros of f) is proved in Legacy `PVChain/Assembly/ResidueSide.cpv_residue_side_tendsto` (3377 lines of support under old API). Pure FM has the abstract infrastructure (`ResidueSideData`, `ModularSideData`, `residueSide_tendsto_of_data`, `modularSide_tendsto_of_data`, `pvChainIdentity`, `discharge_pvChain_full`) but no constructor. |
| **7 Delete Legacy substrate** | ⏳ Blocked on 6 | Will happen naturally once Phase 6 lands. |
| **8 Mathlib PR polish** | 🟢 Can start now for Chain 1 | The 81 Legacy-free pure FM files are PR-ready today, independent of Phase 6. |

**Conclusion:** The one genuinely remaining technical hurdle is Phase 6 (crossing-case
residue side in new API). Phases 2, 7 will fall out from Phase 6. Phase 8 (Chain 1
PR submissions) can proceed in parallel immediately.

## Phase structure (original, with status above)

### Phase 0 — Consolidation & cleanup (3 days)

Concrete, bounded wins that improve the PR surface without touching the proofs.

- [ ] **0.1** Merge duplicate `ModularInvariance`: pure FM `ModularInvariance.lean` (330 lines, `*FM` suffixes) vs `Legacy/ValenceFormula/ModularInvariance.lean` (386 lines, unsuffixed + cusp-vanishing lemmas). Decide on one canonical version, preserve the cusp-vanishing extras, drop the `FM` suffix.
- [ ] **0.2** Drop `FM` suffix from pure ForMathlib where Legacy-suffix-collision is gone. Candidates: `modularFormCompOfComplexFM`, `ord_add_one_eqFM`, `fdBoxFM`, `OrbitFM`, `NonEllOrbitFM`, `ordOrbitFM`, `ordOrbitQFM`, `orbFM`, etc. Large mechanical rename.
- [ ] **0.3** Verify every pure ForMathlib file uses only `push Not` (not `push_neg`) — already done this session, keep checked.
- [ ] **0.4** Mark the oracle-form theorems (`generalizedResidueTheorem`, `HigherOrderAssembly.generalizedResidueTheorem_of_cancel_oracle`, `HigherOrderCancel.generalizedResidueTheorem_with_hCancel`) with `TODO` docstrings pointing at Phase 1.

**Exit criterion:** Pure FM has no `*FM` naming suffixes, no `push_neg`, and the valence-formula statement compiles unchanged.

### Phase 1 — Close the oracle on `generalizedResidueTheorem` (1–2 weeks)

Currently `generalizedResidueTheorem` in `ForMathlib/GeneralizedResidueTheorem.lean` takes four hypotheses that should follow from Conditions A'/B:

```lean
(hCancel : HasCauchyPVOn S (fun z => f z − principalPartSum …) γ 0)
(hPV_sing : HasCauchyPVOn S (principalPartSum …) γ (2πi · Σ w·res))
(hI_sing : ∀ ε > 0, IntervalIntegrable (cpvIntegrandOn S (principalPartSum …) …))
(hI_rem : ∀ ε > 0, IntervalIntegrable (cpvIntegrandOn S (f − principalPartSum …) …))
```

The plan's PR E1 ("Higher-Order Cancellation Assembly") is where these come from. Work here:

- [ ] **1.1** `hI_sing` / `hI_rem`: interval integrability of the cutoff integrands. For simple poles these are standard; for higher-order poles they follow from the `SectorCurve` bounds. Pure-FM `SectorCurve.lean` exists but is not yet wired to `GeneralizedResidueTheorem`.
- [ ] **1.2** `hPV_sing`: CPV of the principal-part sum equals `2πi · Σ w·res`. Reduces (via `HasCauchyPVOn.add` / `_.smul`) to CPV of a single simple-pole term, which is `SimplePoleIntegral.pv_integral_simple_pole`.
- [ ] **1.3** `hCancel`: the remainder after subtracting the principal part has zero CPV. This is the genuine content of Condition A' (flatness at crossings) and Condition B (Laurent compatibility). Reduce it to the Dixon theorem (`DixonTheorem.dixonFunction_eq_zero`) applied in a neighborhood of the curve.
- [ ] **1.4** Produce `generalizedResidueTheorem_closed`: the variant that derives `hCancel`, `hPV_sing`, `hI_sing`, `hI_rem` from `SatisfiesConditionA' γ f S poleOrder ∧ SatisfiesConditionB γ f S`. This is the "real" HW Theorem 3.3.
- [ ] **1.5** Specialize: `generalizedResidueTheorem_simplePoles` derives the closed form for the simple-pole case with no geometric conditions (falls out automatically via `conditions_automatic_for_simplePoles`).

**Exit criterion:** Every theorem in `GeneralizedResidueTheorem.lean` / `HigherOrderAssembly.lean` / `HigherOrderCancel.lean` takes only A'/B (or simple-pole) hypotheses, not the four oracle hypotheses.

**Dependency:** This phase touches only pure FM (Chain 1) and is independent of the Legacy port. It should be done first because:
1. The new-API proof of `pv_chain_identity` in Phase 6 invokes `generalizedResidueTheorem_closed`.
2. Chain 1 PRs (Phase 8) can ship to mathlib independently once this phase is done.

### Phase 2 — Port `fdBoundary` geometry (1 week)

`Legacy/ValenceFormula/Boundary/{Bounds,Smooth}.lean` (≈ 1240 lines) and `Legacy/ValenceFormula/OnCurvePV/{Basic,EndpointCorner,Main}.lean` (≈ 1790 lines) prove:
- `fdBoundary_H` on `[0,5]` has a `PiecewiseC1Curve` structure (smoothness off `{1,2,3,4}`).
- Avoidance / bound lemmas for points in the FD.
- On-curve PV existence at endpoints / corners.

Pure FM already has `FDBoundary.lean` defining `fdBoundaryFun H` on `[0,1]`, `FDBoundaryPath.lean`, `FDWindingDataFullSeg1Seg4.lean`, `FDWindingDataFullAssembly.lean`. These already express the FD boundary as a `PiecewiseC1Immersion (fdStart H) (fdStart H)`. **Most of Phase 2's content is already present in pure FM — this phase is about closing a few gaps and eliminating the Legacy dependency**.

- [ ] **2.1** Audit `Legacy/ValenceFormula/Boundary/*` for lemmas not already covered by pure-FM `FDBoundaryPath` / `FDBoundary` / `SegmentAnalysis`. Port any genuinely new ones.
- [ ] **2.2** Audit `Legacy/ValenceFormula/OnCurvePV/*` vs pure-FM on-curve CPV infrastructure. Port gaps.
- [ ] **2.3** Delete `Legacy.FDBoundaryH` bridge: eliminate all references to `fdBoundary_H` (the `[0,5]` function) in favour of `fdBoundaryFun` / `PiecewiseC1Path`.
- [ ] **2.4** Delete `Legacy.FDBoundaryReparametrization` bridge (no longer needed once `fdBoundary_H` is gone).

**Exit criterion:** No Legacy file references `fdBoundary_H`. `Legacy/FDBoundaryH.lean` and `Legacy/FDBoundaryReparametrization.lean` deleted.

### Phase 3 — Port winding weights at elliptic points (2 weeks)

`Legacy/ValenceFormula/WindingWeights/{I,Rho,RhoPlusOne,Common}.lean` total **3351 lines** and instantiate the (old-API) single-crossing computation at the three elliptic points:

- `i`: smooth crossing → winding = −1/2
- `ρ`, `ρ+1`: 60° corners → winding = −1/6 each

Pure FM has `SingleCrossing.lean` with `SingleCrossingData` / `AsymmetricCrossingData` and the master theorems `HasGeneralizedWindingNumber.of_singleCrossing_neg_half` / `of_singleCrossing_neg_sixth`. It also has instantiations in `ArcFTCAtI.lean`, `ArcGenericFTCProvider.lean`, `CornerFTCAtRho.lean`, `Seg1FTCProvider.lean`, `Seg4FTCProvider.lean`, `CrossingAtI.lean`, `CrossingAtRho.lean`, `BoundaryWinding{,ArcProof,Seg1Proof,Seg4Proof}.lean`. **Most of Phase 3's content is already in pure FM**.

- [ ] **3.1** Verify the pure-FM winding-weight proofs deliver `HasGeneralizedWindingNumber γ i (-1/2)`, `HasGeneralizedWindingNumber γ ρ (-1/6)`, `HasGeneralizedWindingNumber γ (ρ+1) (-1/6)` without any import from Legacy. Close any remaining gaps.
- [ ] **3.2** Identify the parts of `Legacy/ValenceFormula/WindingWeights/*` that are still consumed by other Legacy files (mostly `PVChain/*`), and rewire those consumers to use the pure-FM versions instead.
- [ ] **3.3** Delete `Legacy/ValenceFormula/WindingWeights/` once unused.

**Exit criterion:** `Legacy/ValenceFormula/WindingWeights/` directory empty, every winding-weight result available via pure FM.

### Phase 4 — Port interior winding (1 week)

`Legacy/ValenceFormula/InteriorWinding.lean` and the `Legacy/ValenceFormula/RectHomotopy/*` files were deleted in the 2026-04-20 consolidation (they weren't in the transitive closure of `ValenceFormulaFinal`). Pure FM has `InteriorWinding.lean`, `InteriorWindingProof.lean`, `InteriorContourIntegral.lean` which prove `HasGeneralizedWindingNumber fdBoundaryFun z (-1)` for `z` in the strict FD interior.

- [ ] **4.1** Verify the pure-FM interior-winding chain is self-contained (no Legacy deps).
- [ ] **4.2** Connect interior winding to the assembly in Phase 6.

**Exit criterion:** Interior winding = −1 available via pure FM without Legacy.

### Phase 5 — Port modular side (1 week)

`Legacy/ValenceFormula/{ModularInvariance,OrbitPairing,OrbitSum}.lean` (≈ 960 lines) contain T-periodicity cancellations for vertical edges, S-transformation identities for arcs, horizontal contour contribution = `2πi · ord_∞`. Pure FM has `ModularInvariance.lean` (FM-suffixed), `OrbitPairing.lean`, `Orbits.lean`, `HorizontalContribution.lean`, `ModularSideProof.lean`, `ModularContourIntegral.lean`.

- [ ] **5.1** Audit `Legacy/ValenceFormula/{ModularInvariance,OrbitPairing,OrbitSum}` for content not in pure FM.
- [ ] **5.2** Rewire `Legacy/ValenceFormula/PVChain/*` modular-side callers to pure-FM versions.
- [ ] **5.3** Delete the three Legacy modular-side files.

**Exit criterion:** Modular-side results available via pure FM; Legacy `{ModularInvariance, OrbitPairing, OrbitSum}` deleted.

### Phase 6 — Port PV chain assembly (2 weeks — heaviest phase)

`Legacy/ValenceFormula/PVChain/*` (7 files, ≈ 3376 lines) is where the valence-formula proof is assembled. The main theorem `pv_chain_identity` (top of `Legacy/ValenceFormula/PVChain.lean`) states:

```
Σ_s gWN'(fdBoundary_H, s) · ord(f, s) = −(k/12 − ord_∞(f))
```

Proved via:
1. **Residue side** (`cpv_residue_side_tendsto`): apply the generalized residue theorem to `logDeriv f` along `fdBoundary_H`. Uses `GeneralizedResidueTheory.Residue.GeneralizedTheoremBase` + `PVInfrastructure/*`.
2. **Modular side** (`cpv_modular_side_tendsto`): compute the CPV directly using T/S invariance + horizontal contribution.
3. **Equate** by Tendsto uniqueness, cancel `2πi`.

The new-API replacement is:

```
∃ L, HasCauchyPVOn (sArc ∪ sVert) (logDeriv f) γ L  -- both sides
L = 2πi · Σ_s gWN(γ, s) · ord(f, s)                 -- residue
L = −2πi · (k/12 − ord_∞)                          -- modular
⇒ Σ gWN·ord = −(k/12 − ord_∞)                      -- uniqueness
```

- [ ] **6.1** Residue side in new API: apply `generalizedResidueTheorem_closed` (from Phase 1) with `f = logDeriv f`, `γ = fdBoundaryFun H` (Phase 2), automatic A'/B for simple poles of `logDeriv`. Gives `HasCauchyPVOn` at the winding-sum value (using Phase 3's weights).
- [ ] **6.2** Modular side in new API: using Phase 5's results, compute `HasCauchyPVOn` at `-2πi·(k/12 − ord_∞)`.
- [ ] **6.3** Uniqueness: `HasCauchyPVOn.unique` (pure-FM `CauchyPrincipalValue.lean`) gives the equality.
- [ ] **6.4** Delete `Legacy/ValenceFormula/PVChain/*` and `Legacy/ValenceFormula/PVChain.lean`.

**Exit criterion:** `pv_chain_identity_new` (new API) proven in pure FM; `Legacy/ValenceFormula/PVChain/` deleted.

**Largest risk:** the old `cpv_residue_side_tendsto` uses `GeneralizedResidueTheory.Residue.GeneralizedTheoremBase` (734 lines of its own), which in turn depends on `Residue/SectorCurve*` (≈ 1550 lines), `PVInfrastructure/*` (≈ 3200 lines). In the new API, all of this substrate lives in pure FM already (`SectorCurve`, `HigherOrderAssembly`, Phase 1's closure). So the port is about *connecting* existing pure-FM parts, not re-proving them.

### Phase 7 — Delete remaining Legacy substrate (1 week)

After Phases 2–6, the `Legacy/GeneralizedResidueTheory/` and `Legacy/ContourIntegral/` directories should only have Legacy-internal users. Verify and delete in dependency order:

- [ ] **7.1** Delete `Legacy/ValenceFormula/` (everything in it).
- [ ] **7.2** Delete `Legacy/ContourIntegral/`.
- [ ] **7.3** Delete `Legacy/GeneralizedResidueTheory/`.
- [ ] **7.4** Delete the 6 bridge files (`ClassicalCPV`, `FDBoundaryH`, `FDBoundaryReparametrization`, `ResidueSide`, `ResidueSideBridge`, `ValenceFormulaBridged`).
- [ ] **7.5** Update `ValenceFormulaFinal.lean` to invoke the new-API proof directly.
- [ ] **7.6** `rmdir LeanModularForms/ForMathlib/Legacy/`.

**Exit criterion:** `LeanModularForms/ForMathlib/Legacy/` no longer exists. `valence_formula_textbook` verified with only standard axioms, proof chain ≤ 100 lines through pure-FM components.

### Phase 8 — Mathlib-PR polish (1 week)

Cut the pure ForMathlib chain into PR-sized slices per the `2026-04-07-mathlib-prs-v2.md` plan and prepare for upstream submission.

- [ ] **8.1** Chain 1 submission order (can go first, independent of valence formula): `PiecewiseC1Path` → `PiecewiseContourIntegral` → `CauchyPrincipalValue` → `GeneralizedWindingNumber` → `SingleCrossing` → `Residue` → `PoincareBridge` → winding theory (Prop 2.2 + 2.3, decomposition, homotopy invariance, integrality, circle bridge) → residue infrastructure → Dixon → Meromorphic Cauchy → HW Theorem 3.3 + Cycles.
- [ ] **8.2** Chain 2 submission order (after Chain 1 lands upstream): FD boundary + winding weights + interior winding + orbit pairing → core identity → textbook valence formula.
- [ ] **8.3** Per PR: run `mathlib4/scripts/style.py` equivalent, verify axioms, verify deprecation-free, check line budgets per the plan (100–300 lines per PR), add mathlib-style docstrings.
- [ ] **8.4** Port the surrounding `ModularForms.*` helpers that bubble up as prerequisite PRs (UpperHalfPlane lemmas, SlashActions lemmas, QExpansion helpers — already in pure FM as small files).

**Exit criterion:** Every file in `LeanModularForms/ForMathlib/` has a corresponding mathlib PR in flight or merged.

---

## Weekly milestones

| Week | Phase | Deliverable | Risk |
|---|---|---|---|
| W1 | 0 + 1.1 | Cleanup consolidation + integrability oracles closed | Low — mechanical + existing infrastructure |
| W2 | 1.2–1.5 | `generalizedResidueTheorem_closed` proved (full HW 3.3) | **Medium** — Dixon integration is the technical crux |
| W3 | 2 | `fdBoundary_H` eliminated, bridges `FDBoundaryH` + `FDBoundaryReparametrization` deleted | Low — pure FM has most of this |
| W4 | 3 | `Legacy/ValenceFormula/WindingWeights/` deleted | Medium — lots of files, need careful rewiring |
| W5 | 4 + 5 | Interior winding + modular side rewired to pure FM | Low — both exist in pure FM |
| W6 | 6.1 + 6.2 | Residue + modular side in new API | **High** — heaviest proof engineering |
| W7 | 6.3 + 6.4 + 7 | Uniqueness + full Legacy deletion | Medium |
| W8 | 8 | PR submission polish | Low |

**Buffer:** 1–2 weeks for the W2 and W6 risks if they slip.

---

## Success metrics

After the plan completes:

1. `LeanModularForms/ForMathlib/Legacy/` does not exist.
2. `valence_formula_textbook` proof chain: pure-FM files only, ≤ 100 lines from top theorem to assembly.
3. `#print axioms valence_formula_textbook` shows only `propext, Classical.choice, Quot.sound`.
4. Every pure-FM file passes mathlib's `lake exe style` (or the `mathlib-quality` skill equivalent).
5. Chain 1 PRs (plan's PR 1–13 + 4b) in flight on mathlib4, independent of Chain 2.
6. Chain 2 PRs (plan's V1–V6) in flight once Chain 1 has landed.

---

## Non-goals

- **No refactoring of `ForMathlib/Modularforms/` or `SpherePacking/`.** Those are unrelated user code.
- **No mathlib-bump during the port.** Pin the current mathlib version (`v4.30.0-rc2`) until the port finishes; bumping mid-port is an unnecessary extra risk.
- **No new mathematics.** Every theorem in the final state should already be provable from today's Legacy content; the port is a faithful re-expression in new API.

---

## What to do if the plan slips

If a phase takes longer than the allocated budget:

- **Phase 1 slip:** Ship `generalizedResidueTheorem` to mathlib in its **oracle form** with a `TODO` pointing to the cancellation assembly. Simple-pole corollary alone is valuable and unblocks many downstream uses.
- **Phase 6 slip:** The entire Chain 1 (through Phase 1) is still shippable to mathlib without blocking on the valence formula. Chain 2 PRs can wait.
- **Phase 8 slip:** Irrelevant to the port itself — the ForMathlib content is usable locally even without upstreaming.

Use the existing `feat/mathlib-prs` branch as the trunk. Cut phase branches off of it for W1–W8. Merge back into `feat/mathlib-prs` at the end of each phase after the build is green.
