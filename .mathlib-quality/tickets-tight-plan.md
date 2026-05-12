# Master Plan: Paper-Faithful HW Theorem 3.3

## End Goal

```lean
theorem hw_3_3_clean
    {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s * residue f s)
```

**Stretch goal** (matching paper exactly): drop `hU` to allow non-open or
unbounded `U`, but the paper itself uses an open set so `IsOpen` is OK.

## Phases

### Phase 1 — Foundations [TIGHT-11] ✅ DONE (2026-05-05)
- [x] 1.1 `ClosedPwC1Curve.lipschitzOnWith_piece` — bound on each closed piece via continuity (`Convex.lipschitzOnWith_of_nnnorm_derivWithin_le`)
- [x] 1.2 `lipschitzOnWith_of_consecutive_pieces` (private) — gluing lemma via strong induction on partition cardinality
- [x] 1.3 `ClosedPwC1Curve.lipschitzWith_extend` — global Lipschitz on ℝ via clamping
- [x] **Outcome**: `hw_3_3_simple_avoidance_paper` no longer needs `hLip`

**Output**: `hw_3_3_simple_avoidance_paper` no longer needs `hLip` argument.

### Phase 2 — Drop `hU_bounded` [TIGHT-12] (REVISED PLAN)

**Investigation (2026-05-05).** `hU_bounded` enters the chain via:
* `hw_3_3_simple_avoidance_paper`
  → `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids`
  → `dixonFunction_eq_zero_of_nullHomologous_open_full`
  → `IsNullHomologous.winding_eventually_zero_cocompact_of_bounded`.

The bottleneck is the last step: bounded U gives `Uᶜ ∈ cocompact`, hence
winding = 0 for cocompact w (since γ avoids w outside U). For unbounded U,
we instead use γ's image being bounded (Lipschitz γ).

**Lemma chain to build**:
- [ ] 2.1 `winding_eventually_zero_cocompact_of_lipschitz` —
  for Lipschitz γ closed, the generalized winding number vanishes for `‖w‖`
  larger than `sup ‖γ.image‖ + (curve length)/(2π)`.
  Proof: combine `dixonH2_norm_le` (gives `|winding| ≤ M_d / (2π(‖w‖ - R))`)
  + `hasGeneralizedWindingNumber_integer_of_closed` (W-3, integer-valued)
  + "integer + < 1 ⟹ = 0".
  ~50 lines.
- [ ] 2.2 `dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded` —
  variant of Dixon's full closure not requiring bounded U.
  Replaces use of `winding_eventually_zero_cocompact_of_bounded` with 2.1.
  ~30 lines (mirrors existing proof structure).
- [ ] 2.3 `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids_unbounded`
  using 2.2. ~20 lines.
- [ ] 2.4 Update `hw_3_3_simple_avoidance_paper` to drop `hU_bounded`.
  ~10 lines.

**Estimated total**: ~110 lines, one focused session.

**Output**: `hw_3_3_simple_avoidance_paper` no longer needs `hU_bounded`.

### Phase 2.5 — Option B refactor of decomposition ✅ DONE (2026-05-05)
- [x] Refactored `laurentHigherOrderPolar` and `laurentHolomorphicRemainder`
  in `HW33LaurentPolarPart.lean` so cancellation hypotheses hold under just
  `hCondB`, no "all-crossed" assumption needed.
- [x] Per-pole guard: `laurentHigherOrderPolarAt s := if IsCrossed γ s then
  polarPartAt s - residue/(z-s) else 0`. New remainder is `f - principalPartSum
  - laurentHigherOrderPolar`.
- [x] **Result**: at uncrossed `s`, the new remainder has zero residue at
  `s` (only k ≥ 2 terms remain), so `∮_γ remainder = 0` follows from Cauchy's
  theorem on null-homologous γ even though remainder isn't globally analytic.
- [x] `laurentAnalyticPartAt` API for the analytic part `g` at crossed poles.

### Phase 3 — Holomorphic remainder analyticity ✅ DONE (2026-05-12)
- [x] 3.1 `f_eq_analyticPart_plus_polarPart_eventually` — local Laurent
  equation in punctured nbhd of crossed `s`. (DONE)
- [x] 3.2 `laurentHolomorphicRemainder_differentiableOn` on `U \ S`. (DONE)
- [x] 3.3 `laurentHolomorphicRemainder_residue_zero` — residue at every `s ∈ S`
  is zero. (DONE 2026-05-12, commit `895bd2a`, `HW33LaurentPolarPart.lean:450`.)
  In fact the proof shows the remainder is **locally analytic** at every `s ∈ S`,
  which is strictly stronger than residue zero.

### Phase 3.5 — Residue calculus prerequisite ✅ DONE (2026-05-12)
- [x] 3.5.1 `residue_add`, `residue_sub` (linearity) — `ResidueLinearity.lean`
- [x] 3.5.2 `residue_const_div_sub` — residue of `c/(z-s)` at `s` equals `c`
- [x] 3.5.3 `residue_const_smul` — scalar multiplication respects residue
- [x] 3.5.4 `residue_finset_sum`
- Commit: `126cb03`. All axiom-clean `[propext, Classical.choice, Quot.sound]`.

### Phase 4-AVOIDANCE — Higher-order avoidance via Dixon (NEW, achievable)
The user observed Dixon's theorem (`dixonFunction_eq_zero_of_nullHomologous_open_full`)
applies to *any* analytic function on `U`, not just simple-pole settings. So
the avoidance case extends from simple-pole to arbitrary-order using
PolarPartDecomposition data.

- [x] 4-AV.1 `PolarPartDecomposition` data structure (DONE)
- [x] 4-AV.2 `contourIntegral_higherOrder_eq_zero_of_avoids` — `∮_γ c/(z-s)^k = 0`
  for `k ≥ 2`, γ closed avoiding `s`, via single-valued antiderivative (DONE)
- [x] 4-AV.3 `simplePolePart` / `higherOrderPart` split + `polarPart_eq_simplePole_add_higherOrder`
  algebraic decomposition (DONE)
- [x] 4-AV.4 `contourIntegral_higherOrderPart_eq_zero_of_avoids` —
  `∮_γ higherOrderPart_s = 0` (DONE)
- [ ] 4-AV.5 `HasSimplePoleAt (f - ∑_s higherOrderPart_s) s` for each `s ∈ S`
  (route through PolarPartDecomposition's analyticRemainder)
- [ ] 4-AV.6 `hw_3_3_higherOrder_avoidance_paper` — final theorem composing
  Phase 4-AV.5 + `hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids`
  + Phase 4-AV.4

### Final extension to MeromorphicAt (paper-faithful)
- [ ] M.1 Build `MeromorphicAt → PolarPartDecomposition` extraction:
  - Use `meromorphicOrderAt_ne_top_iff` to get `f =ᶠ (z-s)^n · g_s` with `g_s` analytic
  - Compute Taylor expansion of `g_s` at `s` (mathlib `iteratedFDeriv`)
  - Construct polar part as `∑_{k=0}^{|n|-1} taylorCoeff_k(g_s) / (z-s)^(|n|-k)`
  - Verify residue (`k = -1` Laurent coefficient) matches mathlib's `residue f s`
- [ ] M.2 `hw_3_3_higherOrder_avoidance_paper` directly from `hMero`

## Concrete proof sketch for TIGHT-12 step 2.1

For future-session execution, the core lemma is:

```lean
private theorem generalizedWindingNumber_eventually_zero_cocompact_of_lipschitz
    {γ : PwC1Immersion x x} {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    ∀ᶠ w in Filter.cocompact ℂ,
      (∀ t ∈ Icc (0:ℝ) 1, γ.toPiecewiseC1Path t ≠ w) ∧
        generalizedWindingNumber γ.toPiecewiseC1Path w = 0
```

Proof outline (~50 lines):
1. Set `R := ‖γ.toPath.extend 0‖ + K`. Then `∀ t ∈ Icc 0 1, ‖γ(t)‖ ≤ R` from Lipschitz.
2. Set `M_d := K`. Then `∀ t ∈ Icc 0 1, ‖deriv γ.extend t‖ ≤ M_d` from Lipschitz.
3. Set `RR := R + M_d / (2π) + 1`. Filter eventually: `‖w‖ > RR ⟹ ‖w‖ > R`.
4. For `‖w‖ > R`: γ avoids w (`‖γ(t) - w‖ ≥ ‖w‖ - R > 0`). Hence
   `hδ : ∃ δ > 0, ∀ t, δ ≤ ‖γ(t) - w‖` with `δ := ‖w‖ - R`.
5. `intervalIntegrable_div_lipschitz γ hδ.2.1 hδ.2.2 hLip` gives integrability
   of `γ'/(γ - w)`.
6. `hasGeneralizedWindingNumber_integer_of_closed γ hδ h_int` gives
   `∃ n : ℤ, HasGeneralizedWindingNumber γ w n`. Hence
   `generalizedWindingNumber γ w = (n : ℂ)`.
7. From `HasGeneralizedWindingNumber γ w n` (avoidance) extract
   `∮_γ 1/(z - w) dz = 2πi · n` (this is the `HasCauchyPV` reduction;
   project's `cauchyPV_eq_contourIntegral_of_avoids` or build inline).
8. Bound `|∮_γ 1/(z - w) dz| ≤ M_d/(‖w‖ - R)` (mirrors `dixonH2_norm_le`'s
   proof with `f = const 1`).
9. Hence `|2π · n| ≤ M_d/(‖w‖ - R)`, i.e. `|n| ≤ M_d/(2π·(‖w‖-R))`.
10. For `‖w‖ > RR = R + M_d/(2π) + 1`, `‖w‖ - R > M_d/(2π) + 1`, so
    `M_d/(2π·(‖w‖-R)) < 1/(1 + 2π/M_d) < 1`. Hence `|n| < 1`.
11. Integer `n` with `|n| < 1` ⟹ `n = 0` (by `Int.lt_one_iff` or similar).
12. Therefore `generalizedWindingNumber γ w = 0`.

Steps 5–7 may need supporting lemmas already in the project. Step 8's
norm bound mirrors `dixonH2_norm_le` exactly.

**Output**: foundational lemma for TIGHT-4 and the global non-avoidance theorem.

### Phase 4 — TIGHT-4 (holo cancel) ✅ DONE (2026-05-12)
- [x] 4.1 `contourIntegral_analytic_eq_zero_of_nullHomologous` — Cauchy's
  theorem for analytic functions on null-homologous closed `PwC1Immersion`,
  thin wrapper over Dixon's theorem. (`HW33HoloCancel.lean`)
- [x] 4.2 `hasCauchyPVOn_continuousOn_of_countable_preimage` — CPV → contour
  bridge via dominated convergence; requires countable preimage of `S` under `γ`.
- [x] 4.3 `h_holo_cancel_of_conditionB` — combines 4.1 + 4.2 + 3.3 via
  `laurentHolomorphicRemainderCorrection` (Riemann removable extension).
- Commit: `8f331d0`. All axiom-clean.
- **Residual hypothesis**: `h_preimage : Set.Countable {t ∈ Icc 0 1 | γ t ∈ ↑S}`.
  Should be eliminated from `PwC1Immersion` structure (non-vanishing derivative ⇒
  isolated zeros of `γ - s` ⇒ finite preimage on each closed piece ⇒ countable).

### Phase 5 — Simple-pole CPV with crossings [hPV_sing for non-avoidance]
- [ ] 5.1 Per-pole CPV at on-curve singularity using generalized winding number
- [ ] 5.2 Multi-pole sum
- [ ] 5.3 `hPV_sing_of_conditionB` final form

**Output**: `hPV_sing` provable.

### Phase 6 — TIGHT-3 (polar cancel)
- [ ] 6.1 Derive geometric data at each crossing from `ClosedPwC1Immersion + hCondB`:
  - [ ] 6.1.1 Tangent existence (left/right derivative limits)
  - [ ] 6.1.2 Tangent non-vanishing
  - [ ] 6.1.3 Continuity on each side (from ContDiffOn)
  - [ ] 6.1.4 Local strict (anti-)monotonicity from non-vanishing tangent + flatness
  - [ ] 6.1.5 Avoidance margin (Proposition 2.2 — finite crossings + compactness)
  - [ ] 6.1.6 Smoothness on outer regions
- [ ] 6.2 Per-pole-per-index singleton CPV via `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`
- [ ] 6.3 Multi-pole multi-index sum: HasCauchyPVOn S laurentHigherOrderPolar
- [ ] 6.4 `h_polar_cancel_of_conditionB` final form

**Output**: `h_polar_cancel` provable.

### Phase 7 — Integrability of `cpvIntegrandOn`
- [ ] 7.1 General lemma: `cpvIntegrandOn` is integrable when integrand is continuous on `U \ S`
- [ ] 7.2 Apply to `laurentHigherOrderPolar`, `laurentHolomorphicRemainder`, `principalPartSum`

**Output**: `hI_polar`, `hI_holo`, `hI_sing` discharged.

### Phase 8 — Compose
- [ ] 8.1 Wrap Phases 4–7 into `hw_3_3_clean` via `hw_3_3_paper`
- [ ] 8.2 Add doc, update `MEMORY.md`, commit

---

## Execution Order

Execute Phase 1 first (Lipschitz foundations), then 2, then in order. Each
phase produces a checkpoint; all phases produce axiom-clean theorems.
