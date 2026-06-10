# Consolidation Campaign II: 39,880 → ≤15,000

**Written**: 2026-06-10, branch `sphere-packing-via-hw33` @ `e3c2bdd`.
**Supersedes**: the Campaign-I plan (88k → 36k arc; see git history of this file for its
ROI tables and process learnings, which still apply).
**Directive**: the whole valence-formula + HW 3.3 + sphere-packing development must fit in
≤15,000 lines without losing or weakening any headline theorem. Bull-at-a-gate proofs are
to be **re-thought into API**, not merely golfed. Exemplar: `SpherePacking/AffineSegment.lean`
(batch 1 of this campaign) cut the contour twins −59% by replacing per-instance lemma
families with one parametrised segment API.

---

## 1. The protected set (statements byte-identical, axioms unchanged)

The 16 blueprint declarations:

| Group | Declarations |
|---|---|
| Crown | `LeanModularForms.hw_3_3_clean_full_mero`, `valence_formula_textbook` |
| HW heads | `HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean`, `…_crossing_compositional`, `…cpv_polarPart_at_multiCrossed_pole_under_condB_corner`, `…cpv_polarPart_at_uncrossed_pole` |
| Valence heads | `valence_formula_orbit_sum_of_pvChain`, `pv_integral_at_i_tendsto`, `pv_integral_at_rho_tendsto`, `pv_integral_at_rho_plus_one_tendsto` |
| Structural defs | `ClosedPwC1Immersion`, `generalizedWindingNumber`, `HasCauchyPVOn`, `IsNullHomologous`, `SatisfiesConditionA'`, `SatisfiesConditionB` |

SpherePacking framework heads (project-protected, not blueprint): `cauchy_integral_zero_pwc1`,
`cauchy_rectangle_zero`, `cauchy_triangle_zero`, `contourIntegral_{rectangle,triangle}Contour_eq`,
`cauchy_semi_infinite_rectangle_eq`, `I12_eq_rectangular_via_triangle`.

**Verification gate for every batch**: `lake build` clean + `lean_verify` on all of the above
(axioms = propext / Classical.choice / Quot.sound) + `#print`-signature snapshot diff for any
file containing a protected decl.

---

## 2. Structural diagnosis (from three parallel deep-analysis passes, 2026-06-10)

### D1 — Two parallel residue theories (the headline)

The valence-formula chain **imports zero HungerbuhlerWasem files** (verified by import-closure
computation and direct grep). The project maintains:

* **Theory A (HW)**: `hw_3_3_clean_full_mero` — CPV of a meromorphic function along a closed
  pw-C¹ immersion that *crosses* poles equals the winding-weighted residue sum. ~12.7k-line
  closure after import hygiene.
* **Theory B (bespoke valence)**: ~10,000 lines — 55% of the valence territory — are
  variations of ONE computation ("log-derivative FTC telescope / PV limit around the pentagon
  with shrinking excision windows"), executed in **two parallel parametrisations** of the same
  boundary ([0,1] `fdBoundaryFun` and [0,5] `fdBoundary_H`, proved equal in
  `FDBoundaryReparametrization` yet each rebuilt from scratch): six FTC-provider files, the
  OnCurvePV existence tree, the BoundaryWinding family, and the WindingWeights triplet —
  with the winding number at ρ literally computed twice from scratch (`WindingWeights/Rho`
  on [0,5]; `CornerFTCAtRho` redoing ρ *and* ρ+1 on [0,1]).

The valence formula is *mathematically* an instance of HW 3.3: the pentagon boundary crosses
the elliptic points i, ρ, ρ+1 where `logDeriv f` has poles — exactly HW 3.3's specialty
(CPV at crossed poles, corner-angle winding weights). Theory B re-proves the general
machinery bespokely at every point. This is the structural form of "bull-at-a-gate".

### D2 — The fat is API-shaped duplication, not golfable slack

Cross-validated instances:
* The "pentagon local forms" family (per-segment chart + hasDerivAt/continuity/eqOn/deriv
  lemmas) is written **~7 times** (~900 lines; ~700 deletable behind one z₀-generic family).
* **~20 left/right mirror pairs** in the HW tree quantify over a bare `γ : ℝ → ℂ`, a filter,
  and a tangent sign — one filter-parametrised statement each (the in-repo proof that this
  works: `FlatnessConditions.tangentDeviation_isLittleO_of_hasDerivWithinAt`).
* A genuine **reflection principle** exists: `fdBoundary_H H (σ t) = −conj (fdBoundary_H H t)`
  (σ = 4−t on [0,4], 9−t on [4,5]) maps ρ ↔ ρ+1 and fixes i — `RhoPlusOne.lean` (670) is
  derivable from `Rho.lean`; half of `I.lean` (855) including both branch-jump computations
  is derivable from its other half; `Seg4FTCProvider` from `Seg1FTCProvider`.
* **Two implementations of "first exit time"** (`LocalDerivedCutoffs` vs `ExitTime`), feeding
  two copies of the same ~100-line split-annihilate-FTC window argument (224 ln and 289 ln).
* Twin 120/199-line sorted-list inductions in `MultiCrossingCPV` with identical skeletons.
* The Laurent-cutoff integrability proof written three times (~85% identical).

### D3 — Free hygiene distorts the picture

* **Five vestigial import lines** (`CrossingDataBuilder.lean:9,11`, `CrossingCPV.lean:9–11`)
  keep 12 modules / 2,142 lines in the HW closure that nothing in it uses (verified
  symbol-by-symbol, found independently by two analysis passes).
* `AsymmetricSingleCrossing.lean` (221) has **zero consumers project-wide**.
* `ViazovskaMagicFunction` carries ~110 lines of legacy-proof helpers with zero consumers.
* GRT `MeasureHelpers` (99) imports `ClassicalCPV` but uses only mathlib (phantom dep).
* Stale module docstrings in ≥5 files advertise deleted theorems (rewrite, don't delete —
  docstrings are not bloat).

---

## 3. End-state architecture (the ≤15k shape)

```
HW 3.3 = THE residue engine                                ~7.5–8.5k
  (MultiCrossing core after mirror/window/induction unification)
Core machinery                                              ~3.0–3.5k
  (curve tower, winding stack, CPV core, NullHomologous, ExitTime)
Valence formula = pentagon instantiation of HW 3.3          ~5.5–6.5k
  (pentagon geometry [one parametrisation], winding-value trio
   [reflection-deduped], orbit/counting arithmetic, conditions-
   checking for logDeriv f, thin bridge)
GRT subtree                                                 ~0.1–0.5k
  (only what hw_3_3's statement chain needs; dyadic PV pipeline
   and generalized-theorem base retired once HW is the engine)
SpherePacking                                               ~2.5k
                                                    ≈ 15.1–16.0k
```

The arithmetic only closes if **Phase R (valence-via-HW re-architecture) succeeds**. Without
it, the floor of the incremental program is ~28–29k. Phase R is therefore the campaign
keystone and gets a feasibility spike before anything depends on it.

---

## 4. Phases

| Phase | Content | Est. Δ | Risk | Gate |
|---|---|---:|---|---|
| **P0 — hygiene** | 5 vestigial import lines; delete `AsymmetricSingleCrossing` (−221); VMF legacy tail (−110); `PVSplitting` vs `ContourIntegral/PVSplit` dedup (−90); stale-docstring rewrites; misc dead (−150) | **−600** | none | build + verify |
| **S — Phase-R spike** (time-boxed, no deletions) | Prove `valence_pentagon_via_hw33`: instantiate `hw_3_3_clean_full_mero` (or `residueTheorem_crossing_paper_faithful_clean`) with γ = pentagon immersion (`Boundary/Smooth` bundling exists), f = `logDeriv F`, S = elliptic points; discharge `SatisfiesConditionA'/B` for simple poles of logDeriv at i, ρ, ρ+1; recover one `pv_integral_at_*` statement as a corollary. Deliverable: a compiling spike file + a go/no-go memo with measured conditions-checking cost | +300 spike | — | compiles or documented blocker |
| **P1 — SpherePacking finish** | batch-2 golf (VMF 861, ContourLimitAtCusp ~480 incl. `rect_seg_*_standard` quadruplet −100, CuspDecay re-clean, ViazovskaResidueRep); true via-triangle rewrite of `I12_eq_rectangular_via_triangle` proof body (drops primitive machinery −199 and unhooks `GRT/CauchyPrimitive` from the SpherePacking closure) | **−600** | low/med | build + verify |
| **P2 — HW program** | L/R mirror collapse behind filter-parametrised API (−325..390); exit-time unification + shared window-splitting lemma (−250..300); twin-induction merge (−140); Laurent-integrability core (−75); CPV singleton-algebra round-trip (−50); `laurentSum` API + golf tail (−350) | **−1,400 to −1,600** | med/high (heart of protected CPV theorems — one concern per batch) | build + verify + signature snapshot |
| **P3 — valence geometry consolidation** (survives both Phase-R outcomes) | F6: make `fdBoundaryFun H t := fdBoundary_H H (5t)` definitional, one transport API (−550); reflection module + `RhoPlusOne` from `Rho` (670→~110) + `I.lean` halving (855→~450); `Seg4` from `Seg1` (−300); local-forms z₀-generic family + `LogFTCPiece` telescope builder (−700 net); `sqrt3` mini-API (−60) | **−2,600 to −3,000** | **hop-0 on the protected trio** — byte-identical restatement + per-batch verify | build + verify + snapshot |
| **P4 = Phase R — valence-via-HW33** (if spike green) | Replace the bespoke existence/assembly layer with the HW instantiation: retire the six FTC providers (CornerFTCAtRho 1,049, ArcGeneric 780, ArcFTCAtI 357, Seg1/Seg4/VertSeg ~1,100), OnCurvePV existence tree (~1,160 of 1,460), BoundaryWinding family (~1,069→~250), PVChain CPV-plumbing (~1,500→~600), bridge thinning (−330), GRT generalized base + dyadic PV pipeline (−3,540), `ClassicalCPV` once the primed layer unhooks (−198) | **−9,000 to −11,000** | high; staged, protected statements re-derived verbatim | per-stage build + verify |
| **P4′ — fallback** (if spike red) | Agent-B incremental program instead: transport-dedup CornerFTCAtRho/ArcFTCAtI from the trio (−1,100), OnCurvePV engine-existence (−750), provider rebase (−700), PVChain golf (−540), GRT PVInfrastructure API-ification (uncertain) | −3,100..−3,800 | med | — |
| **P5 — second wave** | HW deep rethink beyond golf (target −1..2k); core-machinery golf (−460); valence-survivor tightening (−700); payload decision on `I34/I5/I6/a_rad` (user call); `polygonContour` generalisation of the contour twins (−175, optional) | **−2,000 to −3,500** | med | — |

### Running totals

| Checkpoint | If Phase R green | If Phase R red |
|---|---:|---:|
| Start | 39,880 | 39,880 |
| After P0+P1 | ~38,700 | ~38,700 |
| After P2+P3 | ~34,500 | ~34,500 |
| After P4 / P4′ | **~24,000–25,500** | ~30,800 |
| After P5 | **~15,000–16,500** | ~28,000–29,000 |

Honest statement: ≤15,000 is reachable **only through Phase R**, and even then P5 must
deliver. The spike is therefore scheduled immediately after P0, before P2/P3 effort is
committed in volume. P2 and P3 are not wasted in either world (HW is the engine in world-R
and load-bearing regardless; P3 consolidates the geometry/trio layer that survives as
Phase R's input).

---

## 5. Sequencing & protocol

1. **P0** (one batch) → **S spike** (one dedicated dispatch, time-boxed) → decision point
   with the user.
2. Then P1 ∥ P2 ∥ P3 in alternating batches (one batch per dispatch, pause between — pacing
   rule), each batch a single concern.
3. P4 staged: providers first (their consumers re-target to the HW instantiation), then
   OnCurvePV, then BoundaryWinding, then GRT retirement; full verify between stages.
4. Every batch: `lake build` + `lean_verify` × 16 protected + snapshot diff; commit + push
   per batch; revert any refactor that can't go green within ~5 iterations.
5. Refresh this file's running totals after each phase; refresh `PROJECT_OVERVIEW.md` at
   campaign end.

## 6. Open decisions (user)

1. **Phase-R go/no-go** after the spike memo.
2. **Payload**: `I34/I5/I6/a_rad` in `ViazovskaMagicFunction` have no consumers but are the
   sphere-packing mathematical payload — keep (costs ~500 toward the budget) or drop until
   the a_rad development resumes?
3. **`ClassicalCPV`/primed-CPV layer**: retire with P4, or keep if the primed
   `generalizedWindingNumber'` API is wanted long-term?

## 7. Cross-validated quick facts (for batch authors)

* Vestigial imports: `HungerbuhlerWasem/CrossingDataBuilder.lean:9,11` (`BoundaryWinding`,
  `AsymmetricSingleCrossing`), `HungerbuhlerWasem/CrossingCPV.lean:9–11` (`SingleCrossing`,
  `AsymmetricSingleCrossing`, `DixonTheorem`).
* Zero-consumer deletions: `AsymmetricSingleCrossing.lean`; VMF legacy helpers
  (`truncated_contour_equivalence`, `truncated_{diagonal,vertical}_eq_primitive_sub`,
  `I12_eq_segment_integral`, `I12_vert_eq_segment`, `segment_integral_add_of_holomorphic`,
  `D_eq_three_terms`, legacy `I12_eq_rectangular`).
* Mathlib has **no** windingNumber development at the pinned rev — no upstream subsumption
  for the winding stack; Dixon machinery must stay (its `generalizedWindingNumber` is the
  protected CPV-based notion).
* `LocalCutoffs` "cutoffs" are exit-time radii, NOT smooth bumps — `exists_smooth_*` is
  irrelevant; the correct unification is `firstExitTime` (ExitTime.lean).
* Reflection σ: seg1↔seg4, arc↔arc, seg5↔seg5; integrand transfer is at integrand level
  (no branch-cut issues); limits check out (−conj(−iπ/3) = −iπ/3).
* `Seg5CuspIntegral` + `CuspDecay` were flagged "heavier rewrite" in the mathlib bump —
  re-clean during P3/P1 respectively (bump-must-not-undo-cleanup rule).
