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

### Phase 2 — Bounded-domain reduction [TIGHT-12]
- [ ] 2.1 Pick a δ-thickening `V := { z : ∃ t, |z - γ t| < δ }` for sufficient `δ`
- [ ] 2.2 Show `γ` is null-homologous in `V` and `V` is bounded open
- [ ] 2.3 Wrap closed-full theorem on `V`, conclude on `U`

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

### Phase 3 — Holomorphic remainder analyticity ✅ partial
- [x] 3.1 `f_eq_analyticPart_plus_polarPart_eventually` — local Laurent
  equation in punctured nbhd of crossed `s`. (DONE)
- [x] 3.2 `laurentHolomorphicRemainder_differentiableOn` on `U \ S`. (DONE)
- [ ] 3.3 `laurentHolomorphicRemainder_residue_zero` — residue at every `s ∈ S`
  is zero. **Needs**: residue calculus API (linearity, residue of `c/(z-s)`,
  analytic ⇒ residue 0). Some of this exists in `ResidueCircleIntegral.lean`
  for analytic functions; linearity for add/sub does not.

### Phase 3.5 — Residue calculus prerequisite (NEW, DEPENDENCY)
- [ ] 3.5.1 `residue_add`, `residue_sub` (linearity)
- [ ] 3.5.2 `residue_const_div_sub` — residue of `c/(z-s)` at `s` equals `c`
- [ ] 3.5.3 `residue_smul_const` — scalar multiplication respects residue
- [ ] 3.5.4 `residue_finset_sum`

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

**Output**: foundational lemma for TIGHT-4 and the global non-avoidance theorem.

### Phase 4 — TIGHT-4 (holo cancel)
- [ ] 4.1 `cauchyIntegral_zero_for_analytic_nullHomologous` — `∮_γ g = 0` for `g` analytic + γ null-hom
- [ ] 4.2 `cpv_tendsto_contour_for_analytic` — CPV → contour integral as ε → 0 (DCT)
- [ ] 4.3 `h_holo_cancel_of_conditionB` — combines 4.1 + 4.2 + 3.3

**Output**: `h_holo_cancel` is provable from `hCondB`.

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
