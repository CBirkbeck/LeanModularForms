# Theorem 3.3 with Paper's Conditions (A)+(B) — Implementation Plan

**Goal:** Replace the `hHigherOrderCancel` hypothesis in `generalizedResidueTheorem_higher_order` with the paper's actual conditions (A) and (B), proving the implication.

**Paper:** Hungerbuhler-Wasem, arXiv:1808.00997v2, Theorem 3.3 (pages 14-15)

**Current state:** `generalizedResidueTheorem_higher_order` is sorry-free but takes a pre-digested `hHigherOrderCancel` hypothesis. The paper's conditions (A) (flatness) and (B) (angle/Laurent compatibility) are defined in `Flatness.lean`, but `SatisfiesConditionB.laurent_compatible` is a `True` placeholder.

---

## Mathematical Argument

At each crossing point z_0 (pole of order N), decompose f into its Laurent series:

```
f(z) = a_{-N}/(z-z_0)^N + ... + a_{-2}/(z-z_0)^2 + a_{-1}/(z-z_0) + g(z)
```

where g is analytic at z_0 and a_{-1} = Res(f, z_0).

The pure residue function is f_res(z) = Res(f,z_0)/(z-z_0). To show PV(f) = PV(f_res), we show each remaining term has zero PV:

1. **Regular part g:** integral = 0 by FTC (g analytic, sector closed). Already proved as `integral_analytic_sectorCurve_eq_zero`.

2. **Higher-order term a_{-k}/(z-z_0)^k (k >= 2):** The PV on a sector curve of angle alpha equals `(e^{i(1-k)alpha} - 1) * epsilon^{1-k} / (1-k)`. This diverges UNLESS `(k-1)*alpha in 2*pi*Z`, in which case `e^{i(1-k)alpha} = 1` and the PV is **identically 0** for all epsilon. This is equation (3.4) from the paper.

3. **Flatness transfer (Condition A):** Ensures PV on actual curve gamma = PV on model sector curve. The error is bounded by `(1/epsilon^n) * Length(connecting arcs)` where `Length = o(epsilon^n)` by flatness, so the error -> 0.

**Condition (B)** says: for each k >= 2 with a_{-k} != 0, `(k-1)*alpha in 2*pi*Z`.

Combined with condition (A), this gives PV(f - f_res) = 0 on each local sector, hence globally `hHigherOrderCancel` holds.

---

## Dependency Graph

```
Task F1 (Flatness.lean)       Task F2 (SectorCurve.lean)
 Laurent coeff def +            PV z^{-n} = 0 on
 Fix Condition (B)              model sector
       |                              |
       v                              v
Task F3 (SectorCurve.lean or new file)
 Flatness transfer: PV on actual curve = PV on model
       |
       v
Task F4 (GeneralizedTheorem.lean)
 Bridge: (A)+(B) ==> hHigherOrderCancel
       |
       v
Task F5 (GeneralizedTheorem.lean)
 Final theorem with (A)+(B) hypotheses
```

**Parallel lanes:**
- **Worker A:** Task F1 (Laurent infrastructure + fix condition B)
- **Worker B:** Task F2 (PV of negative powers on model sector)
- **Worker C:** Task F3 (flatness transfer) — can start once F1's definitions are done
- **Sequential:** Tasks F4, F5 (after F1-F3 complete)

---

## Task F1: Laurent Coefficient Infrastructure + Fix Condition (B)

**File:** `Flatness.lean` (modify) + possibly new `LaurentCoeff.lean`
**Parallel with:** Task F2
**Blocked by:** Nothing

### F1a: Define `laurentCoeff`

Define the k-th Laurent coefficient of a meromorphic function at a point.

Given `hf : MeromorphicAt f s`, there exists an analytic `g` with `g(s) != 0` and pole order N such that `f(z) = g(z) / (z - s)^N` near s. The Laurent coefficient at index -j (j >= 0) is the Taylor coefficient of g at index (N - j).

```lean
/-- The coefficient of (z - s)^{-k} in the Laurent expansion of f at s.
    Requires MeromorphicAt f s. Returns 0 for k outside the principal part. -/
noncomputable def laurentCoeff (f : C -> C) (s : C) (hf : MeromorphicAt f s) (k : N) : C :=
  if h : k <= poleOrder f s hf then
    -- Taylor coefficient of the analytic part at index (poleOrder - k)
    (hf.analyticPart s).taylorCoeffWithin (poleOrder f s hf - k)
  else 0
```

The exact API depends on what mathlib provides for `MeromorphicAt`. Key properties needed:
- `laurentCoeff f s hf 1 = residueAt f s` (residue is the -1 coefficient)
- Laurent expansion: `f(z) = sum_{k=1}^{N} laurentCoeff f s hf k / (z-s)^k + g(z)` near s
- For simple poles: `laurentCoeff f s hf k = 0` for k >= 2

**Investigation needed:** Check what `MeromorphicAt` provides in current mathlib for extracting the analytic part and its Taylor coefficients. The exact definition may need adjustment.

**Alternative (simpler):** Avoid defining `laurentCoeff` as a standalone function. Instead, state condition (B) existentially:

```lean
structure SatisfiesConditionB_at (...) : Prop where
  angle_rational : ...
  /-- There exists a Laurent decomposition where higher-order terms
      satisfy the angle compatibility -/
  laurent_compatible :
    exists (N : N) (c : N -> C) (g : C -> C),
      AnalyticAt C g s /\
      (forall^f z in nhdsNE s, f z = g z + residueAt f s / (z - s) +
        sum_{k in Finset.range N} c k / (z - s) ^ (k + 2)) /\
      (forall k, k < N -> c k != 0 ->
        exists m : Z, ((k + 1 : R)) * angleAtCrossing gamma t0 ht0 = m * (2 * Real.pi))
```

This avoids needing a standalone `laurentCoeff` def and is self-contained.

### F1b: Update `SatisfiesConditionB`

Replace the placeholder:

```lean
-- OLD:
laurent_compatible : True

-- NEW (per-crossing-point version):
laurent_compatible : forall s in S0, forall t0 in Icc gamma.a gamma.b,
  gamma.toFun t0 = s -> forall ht0 : t0 in Ioo gamma.a gamma.b ->
    SatisfiesConditionB_at gamma f s t0 ht0
```

### F1c: Update `conditions_automatic_simple_poles`

For simple poles (order 1), there are no higher-order Laurent coefficients, so condition (B) reduces to just `angle_rational`. The proof should be straightforward.

### F1d: Define `poleOrder`

Extract the pole order from `MeromorphicAt`:

```lean
noncomputable def poleOrder (f : C -> C) (s : C) (hf : MeromorphicAt f s) : N :=
  (-hf.order).toNat  -- hf.order is negative for poles
```

---

## Task F2: PV of z^{-n} = 0 on Model Sector Curve

**File:** `SectorCurve.lean`
**Parallel with:** Task F1
**Blocked by:** Nothing

### Statement

```lean
theorem pv_sector_negative_power (r : R) (hr : 0 < r) (alpha : R)
    (halpha_nonneg : 0 <= alpha) (halpha_le : alpha <= 2 * Real.pi)
    (n : N) (hn : 2 <= n)
    (h_angle : exists k : Z, (n - 1 : Z) * alpha = k * (2 * Real.pi)) :
    CauchyPrincipalValueExists' (fun z => z ^ (-(n : Z))) (sectorCurve r alpha) 0 3 0 /\
    cauchyPrincipalValue' (fun z => z ^ (-(n : Z))) (sectorCurve r alpha) 0 3 0 = 0
```

### Proof Strategy

Explicit 3-segment computation. For each epsilon > 0 (with epsilon < r):

- **Seg1** (radial, t in [epsilon/r, 1]): `integral = r^{1-n}/(1-n) * (1 - (epsilon/r)^{1-n})`
- **Seg2** (arc, t in [1, 2]): `integral = r^{1-n}/(1-n) * (e^{i(1-n)alpha} - 1)`
- **Seg3** (radial, t in [2, 3-epsilon/r]): `integral = -r^{1-n} * e^{i(1-n)alpha}/(1-n) * (1 - (epsilon/r)^{1-n})`

Sum = `r^{1-n}/(1-n) * (e^{i(1-n)alpha} - 1) * (epsilon/r)^{1-n}`

When `(n-1)*alpha in 2*pi*Z`: `e^{i(1-n)alpha} = 1`, so the factor `(e^{i(1-n)alpha} - 1) = 0`, making the entire sum **identically 0** for all epsilon. Hence PV exists trivially and equals 0.

### Proof Steps

1. Compute the cutoff integral on each segment (reuse `deriv_sectorCurve_seg1/2/3`, `sectorCurve_seg1/2/3`)
2. Evaluate each segment integral in closed form
3. Sum the three contributions
4. Apply the angle condition to show the sum = 0
5. Conclude PV exists (constant sequence 0 -> 0) and PV = 0

**Estimated difficulty:** Medium. The segment integrals involve `t^{-n}` which needs careful integration (antiderivative `t^{1-n}/(1-n)` for n >= 2). The algebraic simplification is the key step.

---

## Task F3: Flatness Transfer Lemma

**File:** `SectorCurve.lean` or new `Residue/FlatnessTransfer.lean`
**Parallel with:** Task F2 (once F1 definitions are available)
**Blocked by:** Task F1 (needs `IsFlatOfOrder` definition — already exists)

### Statement

```lean
theorem pv_flat_curve_eq_pv_model_sector
    (gamma : R -> C) (t0 : R) (s : C) (hgamma_t0 : gamma t0 = s)
    (r : R) (hr : 0 < r) (alpha : R)
    (n : N) (hn : 2 <= n)
    (hflat : IsFlatOfOrder gamma t0 n)
    (h_tangent_match : ...) -- tangent directions match the sector
    :
    Tendsto (fun epsilon =>
      (integral of f on gamma with cutoff epsilon) -
      (integral of f on sectorCurve with cutoff epsilon))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

### Proof Strategy (from paper, page 14)

The difference between the PV on the actual curve and the model sector is bounded by the integral over the connecting arcs alpha_1, alpha_2:

```
|PV_gamma - PV_sector| <= (1/epsilon^n) * Length(alpha_1 + alpha_2)
```

Flatness of order n means the curve stays within `o(|gamma(t) - s|^n)` of the tangent line. For |gamma(t) - s| ~ epsilon, the connecting arcs have length `o(epsilon^n)`. So the bound is `(1/epsilon^n) * o(epsilon^n) -> 0`.

### Key Sub-steps

1. **Construct connecting arcs:** Given the actual curve gamma near t0 and the model sector curve, build arcs connecting them at distance epsilon from s
2. **Bound arc length via flatness:** Use `IsFlatOfOrder` to show arc length = o(epsilon^n)
3. **Bound the integrand:** |z^{-n}| = 1/epsilon^n on the arcs
4. **Conclude:** product bound -> 0

**Estimated difficulty:** Hard. This is the most geometrically involved task. The construction of connecting arcs and the precise bounds require careful analysis. Consider an alternative approach:

**Alternative (avoid explicit arc construction):** Instead of comparing PV on gamma with PV on sector, directly show PV(z^{-k}) = 0 on the actual curve using the flatness bound:
- The integral ∫_{|gamma(t)-s|>epsilon} (gamma(t)-s)^{-k} * gamma'(t) dt decomposes into contributions from each side of the crossing
- Flatness ensures the contributions from opposite sides cancel (they approximate the sector contributions, which cancel by Task F2)

---

## Task F4: Bridge Lemma — (A)+(B) implies hHigherOrderCancel

**File:** `GeneralizedTheorem.lean`
**Blocked by:** Tasks F1, F2, F3
**Sequential**

### Statement

```lean
theorem conditionsAB_imply_higherOrderCancel
    (gamma : PiecewiseC1Immersion)
    (f : C -> C) (S0 : Finset C)
    (hMero : forall s in S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' gamma f S0 poleOrder)
    (hCondB : SatisfiesConditionB' gamma f S0)
    (... regularity hypotheses ...) :
    Tendsto
      (fun epsilon =>
        (integral of cpvIntOn S0 f gamma epsilon t) -
        (integral of cpvIntOn S0 f_res gamma epsilon t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
```

### Proof Strategy

1. **Localize:** For small epsilon, the difference integrand is supported near crossing points (away from crossings, f and f_res agree up to analytic terms)
2. **Per-crossing decomposition:** At each crossing point s with angle alpha:
   - Extract Laurent decomposition: f = Res/(z-s) + higher_order + analytic
   - f_res near s = Res/(z-s) (plus contributions from other poles, which are analytic at s)
   - So f - f_res near s = higher_order + (analytic stuff)
3. **Higher-order terms vanish:** By Task F2 (PV = 0 on model sector) + Task F3 (flatness transfer)
4. **Analytic terms vanish:** By `integral_analytic_sectorCurve_eq_zero` (already proved)
5. **Sum over all crossings:** Finite sum of terms each -> 0 gives total -> 0

### Key Infrastructure Needed

- Laurent decomposition from `MeromorphicAt` (Task F1)
- `pv_sector_negative_power` (Task F2)
- Flatness transfer (Task F3)
- `multipointPV_diff_tendsto` from MultipointPV.lean (for localization)

**Estimated difficulty:** Hard. Requires careful integration of all previous results.

---

## Task F5: Final Theorem Statement

**File:** `GeneralizedTheorem.lean`
**Blocked by:** Task F4
**Sequential**

### Statement

```lean
/-- **Generalized Residue Theorem (Theorem 3.3, Hungerbuhler-Wasem)**
Matching the paper's hypotheses: conditions (A) (flatness) and (B) (angle/Laurent
compatibility) replace the abstract hHigherOrderCancel hypothesis. -/
theorem generalizedResidueTheorem_3_3
    (U : Set C) (hU : IsOpen U) (hU_convex : Convex R U)
    (S : Set C) (hS_in_U : ...) (hS_discrete : ...) (hS_closed : IsClosed S)
    (S0 : Finset C) (hS0_subset : ...)
    (f : C -> C) (hf : DifferentiableOn C f (U \ S0))
    (gamma : PiecewiseC1Immersion)
    (hgamma_closed : ...) (hgamma_in_U : ...) (hS_on_curve : ...)
    (hMero : forall s in S0, MeromorphicAt f s)
    -- Paper's Condition (A): flatness at each crossing
    (hCondA : SatisfiesConditionA' gamma f S0 poleOrder)
    -- Paper's Condition (B): angle/Laurent compatibility at each crossing
    (hCondB : SatisfiesConditionB' gamma f S0)
    -- Regularity:
    (hgamma_meas : ...) (h_no_endpt_cross : ...)
    (hC2_cross : ...) (h_cont_deriv_cross : ...) :
    cauchyPrincipalValueOn S0 f gamma.toFun gamma.a gamma.b =
      2 * Real.pi * I * sum s in S0,
        generalizedWindingNumber' gamma.toFun gamma.a gamma.b s * residueAt f s
```

### Proof

```lean
  exact generalizedResidueTheorem_higher_order U hU hU_convex S ... f gamma ...
    (conditionsAB_imply_higherOrderCancel gamma f S0 hMero hCondA hCondB ...)
    ...
```

One line: derive `hHigherOrderCancel` from Task F4, then apply the existing theorem.

---

## Risk Assessment and Alternatives

| Task | Difficulty | Risk | Mitigation |
|------|-----------|------|------------|
| F1 (Laurent coeff) | Medium | mathlib API for MeromorphicAt may be limited | Use existential formulation (avoid standalone laurentCoeff def) |
| F2 (PV z^{-n} = 0) | Medium | Explicit integral computation may be tedious | Follow pattern of existing `pv_sector_cutoff_eq` |
| F3 (Flatness transfer) | **Hard** | Geometric arc construction is complex | Alternative: direct cancellation argument using flatness bounds |
| F4 (Bridge) | **Hard** | Combines all infrastructure | Can be proved modularly per-crossing-point |
| F5 (Final theorem) | Easy | Just applies F4 | Trivial once F4 is done |

**If Task F3 proves too hard:** An intermediate milestone is to state the theorem with a "per-crossing-point PV cancellation" hypothesis instead of raw (A)+(B). This is strictly stronger than `hHigherOrderCancel` (it gives local control) but weaker than (A)+(B):

```lean
-- Intermediate version: per-crossing PV cancellation
(hLocalCancel : forall s in S0, forall t0, gamma.toFun t0 = s ->
  t0 in Ioo gamma.a gamma.b ->
  Tendsto (fun epsilon => PV_local f f_res gamma s t0 epsilon)
    (nhdsWithin 0 Ioi) (nhds 0))
```

---

## Worker Assignment Summary

| Worker | Tasks | Can Start | Blocked Until |
|--------|-------|-----------|---------------|
| **A** | F1 (Laurent + condition B) | Immediately | -- |
| **B** | F2 (PV z^{-n} on sector) | Immediately | -- |
| **C** | F3 (flatness transfer) | After F1 defs available | F1 definitions |
| **Any** | F4, F5 (bridge + final) | After F1-F3 | All of F1, F2, F3 |

**Tasks F1 and F2 are fully independent and can run in parallel immediately.**
**Task F3 depends only on the IsFlatOfOrder definition (already exists), so can start early.**
