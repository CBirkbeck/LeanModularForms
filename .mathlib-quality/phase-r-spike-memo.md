# Phase-R spike memo — 2026-06-10

Artifact: `LeanModularForms/ForMathlib/PhaseRSpike.lean` (589 lines, builds clean,
2 annotated sorries confined to the clean-wrapper demo §8; **the compositional route
is sorry-free** and `lean_verify`-clean: `propext / Classical.choice / Quot.sound`).
Root `lake build LeanModularForms` untouched and green (8,561 jobs).

## Verdict: **GO — with two binding caveats**

HW 3.3 *does* replace the bespoke pentagon PV machinery, with one architectural
correction and one scope correction:

1. **Entry point caveat.** The protected crown `hw_3_3_clean_full_mero` is **not
   directly instantiable** on the pentagon (or on any contour that crosses a pole on
   a *curved* piece). Its `hCondA` hypothesis demands `IsFlatOfOrder γ t₀ N` where
   `N = (PolarPartDecomposition.ofMeromorphicWithCondB …).order s =
   (mero_laurent_data_exists hMero).choose` — a `Classical.choose`-opaque natural.
   The existential admits every `N ≥ 1` (pad with zero coefficients), so `N = 1` is
   not provable; on the curved arc flatness fails for every `n ≥ 2` (deviation is
   `Θ(dist²)`), so the hypothesis is genuinely undischargeable as stated. The
   correct engine is one layer down: **`residueTheorem_crossing_compositional`**,
   which takes a *caller-supplied* `PolarPartDecomposition` — built by hand with
   `order ≡ 1`, the condition-A′ obligation becomes `isFlatOfOrder_one` (generic)
   and condition B's corner form is **vacuous for simple poles**. The spike proves
   the full pentagon instance this way with zero sorries.
   (Why nobody noticed: the only prior instantiations — rectangle/triangle, `S = ∅`
   or straight-line crossings — have flatness at ALL orders, so the opacity is
   harmless there. The pentagon is the first curved-crossing client.)
   *Fix option*: make `mero_laurent_data_exists` return the canonical minimal `N`
   (via `meromorphicOrderAt`); est. 60–120 lines in `LaurentExtraction.lean`, def-body
   change only — every protected statement stays byte-identical, but the *meaning* of
   the crown's `hCondA` hypothesis improves (becomes dischargeable). Needs user
   sign-off under the protected-set rules.

2. **Scope caveat (the value anchors).** HW 3.3 delivers CPV **existence** and the
   residue-sum **shape** `2πi·Σ w(s)·res(s)` generically — it does not and cannot
   evaluate `w(γ, i) = −1/2`, `w(γ, ρ) = w(γ, ρ+1) = −1/6`. The protected trio
   `pv_integral_at_{i,rho,rho_plus_one}_tendsto` *are* those numeric anchors (the
   spike extracts `w(γ,i) = −1/2` by uniqueness of limits between the HW conclusion
   and the protected statement, then recovers the protected statement verbatim —
   an honest round trip). So P4 retires the *existence/assembly* layer (~9–11k) while
   the trio survives as the anchor layer, slimmed by P3's reflection-dedup as planned.
   Blueprint wording should present the trio as winding-value anchors feeding the HW
   instantiation, not as corollaries of it.

## Per-hypothesis cost table

Status = on the spike's test instance (`f = (z−i)⁻¹`, `S = {i}`, `U` = upper
half-plane, pentagon at height `H > √3/2`). Costs = incremental for the real
integrand `logDeriv F` (simple poles at zeros of `F`: at i, ρ, ρ+1 crossed by the
contour, plus uncrossed interior zeros).

| Hypothesis (compositional route) | Status | Cost for `logDeriv F` | Ingredients |
|---|---|---|---|
| `hU_open, hU_ne, hS_in_U, hx_notin_S` | proved, 12 ln | ~same (zeros lie in the open half-plane; basepoint `1/2+Hi` off zeros needs `F(fdStart H) ≠ 0` — pick `H` above the zero-free cusp height, already a valence-chain fact) | spike §4–5; `CuspDecay`-side bounds |
| `hf : DifferentiableOn (U \ S)` | proved, 4 ln | in-tree for `logDeriv` (valence chain differentiability off zeros) | `ResidueSideInfra`, `ModularInvariance` |
| `hMero : MeromorphicAt at each s` | proved, 2 ln | `hasSimplePoleAt_logDeriv_of_zero'` (in-tree) → `MeromorphicAt`; ~15 ln glue | `PVChain/ResidueSideInfra.lean` |
| `h_null : IsNullHomologous` | proved, 25 ln | **identical — zero extra** (same contour, same `U`) | `RectangularContour.IsNullHomologous.of_convex_open` + `Boundary/Bounds.fdBoundary_H_im_pos` + reparametrisation |
| by-hand `PolarPartDecomposition`, `order ≡ 1` | proved, 30 ln | the ONE genuinely new lemma: `logDeriv F − Σ_s n_s/(z−s)` extends differentiably to `U_trunc`; per-zero data in-tree (`HasSimplePoleAt`), assembly via removable-singularity; **est. 80–150 ln (risk: 250)** | `ResidueSideInfra` + `LaurentExtraction.residue_of_laurent_expansion` + mathlib removable singularity |
| `residue_eq` field (`res(logDeriv F, s) = ord_s F`) | proved for test fn, 8 ln | from `HasSimplePoleAt` coeff + `residue_of_laurent_expansion`; ~20 ln/uniform | same |
| crossings finset (+ completeness) | proved, 2 ln — **abstract**; no `γ t = i ↔ t = 2/5` needed | identical | `Crossing.crossings_finset_of_endpts_off` |
| `hCondA′` (flatness, order 1) | proved, 3 ln | identical — `isFlatOfOrder_one` is generic incl. corners | `FlatnessConditions` |
| `hCondB` corner form (`h_B`) | proved, 1 ln — **vacuous** (simple poles) | identical: all poles of `logDeriv F` simple ⇒ vacuous; **no angle computation anywhere** | — |
| `h_simple_cpv` (CPV existence at crossed pole) | proved, 2 ln — **generic** | identical per crossed pole | `hasCauchyPV_inv_sub_multiCrossing_corner` |
| per-pole CPV (crossed) | proved, 12 ln | ×3 elliptic points, ~40 ln | `cpv_polarPart_at_multiCrossed_pole_under_condB_corner` |
| per-pole CPV (uncrossed interior) | n/a in test | `cpv_polarPart_at_uncrossed_pole` (generic) + winding value `w = −1` from `InteriorWinding`/`InteriorContourIntegral` (survives, ~modest) | `Crossing.lean`, `InteriorWinding` |
| winding values at i, ρ, ρ+1 | anchored on protected `pv_integral_at_i_tendsto` (round trip demonstrated) | the trio stays (protected); P3 dedup applies | `WindingWeights/*` |
| — clean route only: `hCondB.angle_rational` | **sorried** | ~25 ln at i with the coarse-partition trick (the two arc "segments" are literally one analytic function; re-partition `{1/5, 3/5, 4/5}` makes i a smooth point ⇒ `angleAtCrossing_smooth`); ρ, ρ+1 are genuine corners: deriv-limit pinning + `arg` arithmetic ~60–90 ln each | spike `eqOn_arc`; `WindingDecomposition.angleAtCrossing_smooth` |
| — clean route only: `hCondA` (choice-based order) | **sorried — undischargeable as stated** | upstream `LaurentExtraction` fix, 60–120 ln | see Verdict caveat 1 |

## The pentagon-immersion bridge: **done, 230 lines actual**

`pentagonContour : ClosedPwC1Immersion (fdStart H)` (spike §1–3) reuses the existing
`[0,1]` `fdBoundaryPC1Path` and adds only the closed-piece data: 4 `EqOn` lemmas
(three `affineSegment` pieces via the campaign's `AffineSegment` API, one arc piece
via the in-tree `ArcCalculus.unitArc` + its `hasDerivAt`), the closed-partition
lemmas, and the structure instance. No `[0,5]` rescale needed. Matches the
`rectangleContour` going rate (~250) as the plan predicted. This is a one-time cost
**already paid by the spike** — promote it out of the spike file in P4 stage 1.
Bonus finding: `fdBoundaryFun`'s two arc branches are the *same* analytic function
(the `2/5` breakpoint is an artifact of the parametrisation), which both shortened
the bundling and gives the cheap route to `angle_rational` at i if ever needed.

## The statement bridge to `pv_integral_at_*` verbatim: **done, ~85 lines actual**

`pv_integral_at_i_tendsto_via_hw33` (spike §7) restates the protected `[0,5]`
Tendsto byte-identically and proves it from the HW route + the winding anchor.
The in-tree `FDBoundaryReparametrization` already had the forward
(`[0,5] → HasCauchyPVOn`) bridge public; the reverse direction needed ~15 lines
(re-derived extend-congruence; its in-tree twin is `private`) plus the
singleton-`cpvIntegrandOn` if-flip and `deriv_sub_const` glue. ρ and ρ+1 will reuse
the same two public reparametrisation lemmas — est. ~40 ln each.

## Total Phase-R cost estimate

**New lines**: ~700–1,100 total —
immersion bundling 230 (paid) + `logDeriv F` decomposition 80–150 (risk 250) +
meromorphy/residue glue ~70 + HW instantiation for the real integrand ~80 +
uncrossed-pole/interior-winding glue ~100 + per-point statement bridges ~150 +
optional `LaurentExtraction` canonical-order fix 60–120.

**Lines retired (P4 targets, per plan §4)**: ~9,000–11,000 —
six FTC providers (~3,286), OnCurvePV existence tree (~1,160), BoundaryWinding
family to anchor-only (~800 of 1,069), PVChain CPV plumbing (~900), GRT generalized
base + dyadic PV pipeline (~3,540), `ClassicalCPV` (198).

**Net ≈ −8,000 to −10,300.** The plan's P4 arithmetic stands.

## Top 3 risks

1. **`residueTheorem_crossing_compositional` is not in the protected set** — yet it
   is now the load-bearing entry point. P2 (HW golf) could refactor it away.
   Mitigation: add it (and `cpv_polarPart_at_multiCrossed_pole_under_condB_corner`'s
   generic-decomp signature, `hasCauchyPV_inv_sub_multiCrossing_corner`,
   `crossings_finset_of_endpts_off`, `canonical_derivLimits_at_crossings_exists`)
   to the project-protected list before P2 batches touch `MultiCrossingCPV`/`Crossing`.
2. **The global `logDeriv F` polar decomposition** (remainder differentiable on all
   of truncated `U`) is the only new mathematics; if the removable-singularity
   assembly fights, 150 ln could become 250–300. It is still bounded and local.
3. **Anchor circularity discipline**: the trio must remain independent of the HW
   instantiation (they feed it). Any P4 batch that "simplifies" a trio proof by
   routing it through the HW conclusion would create a cycle with the valence
   assembly. Gate: import-direction check `WindingWeights ↛ HW-instantiation files`.

## Recommended P4 staging (GO)

1. **Promote** `pentagonContour` + EqOn/partition lemmas from the spike into
   `ForMathlib/PentagonContour.lean`; extend the protected list per Risk 1.
2. **Decide** the `LaurentExtraction` canonical-order fix (user call): ship it to
   make the crown wrapper honest, or standardise on the compositional entry.
3. **Build the real-integrand instance**: by-hand `PolarPartDecomposition` for
   `logDeriv F` + the compositional instantiation, landing exactly in the
   `HasCauchyPVOn (sArcOfS S ∪ sVertOfS S) (logDeriv …) γ (Σ …)` shape that
   `ResidueSideBridge`/`PVChainProof` already consume.
4. **Retarget consumers, then retire**: OnCurvePV existence tree → six FTC
   providers → PVChain plumbing, verifying the protected trio + valence head after
   each stage.
5. **Slim** BoundaryWinding/WindingWeights to anchor-only (coordinates with P3's
   reflection dedup).
6. **Retire** GRT generalized base + dyadic pipeline; `ClassicalCPV` per user
   decision (plan §6.3).

## Surprises worth recording

* The crown's `hCondA` is undischargeable for ANY curved-crossing instance — the
  hypothesis has effectively never been exercised (all prior clients straight-line).
* Condition B costs *nothing* in the compositional route for simple poles (corner
  form vacuous); the entire angle apparatus is unnecessary for the valence formula.
* Crossing-set identification (`γ t = i ↔ t = 2/5`) — a serious line-item in the
  bespoke chain — is not needed at all: the abstract finite crossing set suffices.
* `fdBoundaryFun`'s arc breakpoint at `2/5` splits one analytic arc into two equal
  halves; recognising this halved the bundling cost.
* The 589-line spike compiled on the first `lake build`.
