# P4 Multi-Day Implementation Plan

**Status:** Drafted 2026-05-21 after three single-session attempts (P4a.1, P4c, P4a.2) all
returned `not feasible at session scale`. This document is the recipe for a dedicated 1–2
week effort.

**Scope:** Unify the four piecewise-C¹ curve types onto the `Path`/`PiecewiseC1Path`
canonical hierarchy. Defined by PROJECT_OVERVIEW.md §3.6 and the four "P4" entries in the
action plan (§Priority 4).

---

## 0. The blocker

The reason P4 cannot be attempted as a single session is a single foundational fact:

> `PiecewiseC1Path x y` is rigidly fixed to the unit interval `[0,1]` because it
> `extends Path x y`, and mathlib's `Path` is defined on `unitInterval`.

Every other curve type lives on a *different* parameter interval:

| Type | Interval | Partition lives in | Smoothness witness |
|---|---|---|---|
| `PiecewiseC1Path x y` | `[0,1]` (via Path) | `Ioo 0 1` | `DifferentiableAt ℝ toPath.extend` |
| `PwC1Immersion x y` | `[0,1]` (via PiecewiseC1Path) | `Ioo 0 1` | inherited |
| `PiecewiseC1Curve` | free `[a,b]`, `a < b` | `Icc a b` (with endpoints) | `DifferentiableAt ℝ toFun` |
| `ClosedPwC1Curve x` | `[0,1]` (via Path) | `Icc 0 1` (with endpoints) | `ContDiffOn ℝ 1 toPath.extend (Icc a b)` |
| `ClosedPwC1Immersion x` | `[0,1]` (via ClosedPwC1Curve) | `Icc 0 1` (with endpoints) | inherited |

The mismatch is *both* (a) the interval (free vs `[0,1]`) and (b) the partition
representation (`Ioo` excluding endpoints vs `Icc` including them). No projection layer
can paper over both at once without ≥100 lines of new affine-reparametrization
infrastructure that delivers zero immediate downstream savings.

**Solution: generalize the canonical type first.** Once `PiecewiseC1Path` is parameterized
by an arbitrary interval `[a,b]`, the structural mismatches collapse, and the unification
becomes mechanical.

---

## 1. Sequencing (4 phases, 1–2 weeks total)

### Phase 1 — Generalize `PiecewiseC1Path` to an arbitrary interval (≈ 3 days)

**Goal:** Replace `PiecewiseC1Path x y` with `PiecewiseC1Path (a b : ℝ) (hab : a < b) (x y : E)`,
where `x = γ a`, `y = γ b`. The underlying carrier is a continuous function `ℝ → E`
restricted to `[a,b]`, *not* a mathlib `Path`. Provide a `toPath : Path x y` projection
when `a = 0 ∧ b = 1` (via affine reparam), but do not make `Path` the underlying structure.

Concrete steps:
1. Rename the current `PiecewiseC1Path x y` to `PiecewiseC1Path01 x y` and keep its
   `extends Path x y`. Mark `@[deprecated]`. (Existing 600+ usages keep working.)
2. Define a fresh `PiecewiseC1Path (a b : ℝ) (hab : a < b) (x y : E)` structure that
   carries `toFun : ℝ → E`, `partition : Finset ℝ ⊆ Icc a b`, `endpoints_in_partition`,
   `continuous_toFun : ContinuousOn toFun (Icc a b)`, and smoothness off the partition.
3. Provide both `Ioo`-style and `Icc`-style smoothness predicates as equivalent variants:
   ```
   theorem differentiable_off_iff_contDiffOn_pieces : ...
   ```
4. Provide affine-reparam isomorphisms:
   ```
   def PiecewiseC1Path.reparamUnit (γ : PiecewiseC1Path a b hab x y) : PiecewiseC1Path01 x y
   def PiecewiseC1Path01.reparamFree (γ : PiecewiseC1Path01 x y) : PiecewiseC1Path 0 1 zero_lt_one x y
   ```
5. Ensure `lake build` green, axioms unchanged on all protected theorems.

**Net line change for Phase 1:** *positive* (∼+200 lines of new infrastructure). This is
the up-front investment that all later phases amortize.

**Risk:** Low (additive, no callers touched).

**Verification:** Build green, `#print axioms ForMathlib.valence_formula_textbook`
yields exactly `[propext, Classical.choice, Quot.sound]`. Same for `hw_3_3_clean_full_mero`.

---

### Phase 2 — Migrate `ClosedPwC1Curve` onto generalized `PiecewiseC1Path` (≈ 3 days)

**Goal:** Restructure `ClosedPwC1Curve x` so it `extends PiecewiseC1Path 0 1 zero_lt_one x x`.
With Phase 1 in place, the `Icc 0 1` partition with `ContDiffOn` smoothness is now
*directly representable* in the canonical type.

Concrete steps:
1. Rewrite `ClosedPwC1Curve.lean` so the structure is
   ```
   structure ClosedPwC1Curve (x : E) extends PiecewiseC1Path 0 1 zero_lt_one x x
   ```
   with the additional `ContDiffOn ℝ 1` requirement folded in via the Phase 1 equivalent
   smoothness predicate.
2. The conversion def at `PaperPwC1Immersion.lean:329`
   (`def toPwC1Immersion (γ : ClosedPwC1Immersion x) : PwC1Immersion x x`) becomes
   `rfl` — modulo the `[0,1]`-specialisation of `PiecewiseC1Path 0 1 _`.
3. `ClosedPwC1Curve.toPiecewiseC1Path` becomes a field projection (`rfl`).
4. The ~600 lines of conversion machinery in `PaperPwC1Immersion.lean:200–600` collapse to
   ~50 lines of explicit `rfl` aliases.
5. ~25 downstream consumer files (HW33Clean.lean among them) keep working because the
   projection chain `γ.toPwC1Immersion.toPiecewiseC1Path` is preserved — though the
   reduction path is now `rfl`-shorter.

**Net line change for Phase 2:** ≈ −500 to −600 (the OVERVIEW's "~600 lines collapse"
estimate lives here).

**Risk:** Medium-high. Touches HW33Clean.lean (protected theorems). The agent must verify
axioms unchanged at every step.

**Verification:** After Phase 2, axiom check both `valence_formula_textbook` and
`hw_3_3_clean_full_mero` should still yield `[propext, Classical.choice, Quot.sound]`. The
`#print` type signature of `hw_3_3_clean_full_mero` must be character-for-character
identical to pre-Phase-2.

---

### Phase 3 — Migrate `PiecewiseC1Curve` (no-endpoints) onto generalized `PiecewiseC1Path` (≈ 2 days)

**Goal:** Replace `ClassicalCPV.lean:53 PiecewiseC1Curve` with a `def` over the generalized
`PiecewiseC1Path a b hab _ _`:
```
def PiecewiseC1Curve := Σ' (a b : ℝ) (hab : a < b) (x y : ℂ), PiecewiseC1Path a b hab x y
```
or, if a structure form is preferred:
```
structure PiecewiseC1Curve where
  a b : ℝ; hab : a < b
  x y : ℂ
  toPath : PiecewiseC1Path a b hab x y
```

Concrete steps:
1. Replace the structure body.
2. Migrate the 198 references across 13 GRT files. Most are projection chains
   `γ.a`, `γ.b`, `γ.partition`, `γ.toFun`, `γ.smooth_off_partition`. They all become
   accessors on the bundled path.
3. The `IsClosed γ` predicate at `ClassicalCPV.lean:80` stays as-is (just renames).
4. `γ.toFun` is now `γ.toPath.toFun`; introduce a coercion to keep proofs short.

**Net line change for Phase 3:** ≈ −100 to −200. Less spectacular than Phase 2 because
the GRT proofs are already well-factored against the structure projections.

**Risk:** Medium. 13 files touched but none are protected.

**Verification:** Axioms unchanged. Build green.

---

### Phase 4 — FD segments via `Path.trans₅` (≈ 1–2 days)

**Goal:** Now that the canonical type accepts arbitrary intervals, re-architect
`FDBoundary.lean` so the 5 segments live on intervals `[0, 1/5], [1/5, 2/5], ..., [4/5, 1]`
naturally rather than via if-then-else.

Concrete steps:
1. Define each segment as a `PiecewiseC1Path (i/5) ((i+1)/5) _ start_i end_i` for
   i = 0, 1, 2, 3, 4.
2. Provide an indexed assembly lemma that glues them into a single
   `PiecewiseC1Path 0 1 zero_lt_one (fdStart H) (fdStart H)`.
3. Optionally: prove `fdBoundaryFun H = assembledPath.toFun`. This is the bridge to the
   25 downstream callers that consume `fdBoundaryFun`.
4. Once the bridge is in place, gradually migrate the 25 callers from `fdBoundaryFun` to
   the assembled path's projection API.

**Net line change for Phase 4:** ≈ −200 to −300, mostly by deleting the 5× hand-rolled
`Continuous.if_le` chain and the redundant `fdBoundaryFun_seg{1..5}_cont` lemmas.

**Risk:** Medium. 25 callers, but no protected theorems. The bridge step at (3) keeps
the migration incremental.

**Verification:** Axioms unchanged. Build green.

---

## 2. Total budget

| Phase | Net lines | Days | Risk |
|---|---|---|---|
| 1 | +200 (investment) | 3 | Low |
| 2 | −500 to −600 | 3 | Medium-high (protected theorems) |
| 3 | −100 to −200 | 2 | Medium |
| 4 | −200 to −300 | 1–2 | Medium |
| **Total** | **−600 to −900** | **9–10 working days** | (managed) |

This matches the OVERVIEW's "1–2 weeks, higher risk" estimate.

---

## 3. Why this sequence and not another

- **Why generalize `PiecewiseC1Path` first?** Because every other unification depends
  on the canonical type accepting `[a,b]` and `Icc`-with-endpoints. Skipping Phase 1
  forces every subsequent phase to invent its own conversion layer (the trap that the
  three session-scale attempts fell into).
- **Why P4a.2 before P4a.1?** Because `ClosedPwC1Curve` already lives on `[0,1]`, so it
  only needs to consume the partition-on-`Icc` extension from Phase 1, not the
  full free-interval extension. Faster validation, smaller downstream risk.
- **Why P4c (FD) last?** Because it benefits from Phase 1's free-interval generalization
  to express seg1..5 on natural intervals `[i/5, (i+1)/5]`. Without Phase 1 it has to
  fight `Path.trans`'s dyadic breakpoint.

---

## 4. Verification protocol (every phase)

After each phase's commit, before declaring the phase complete:

1. `cd ~/Documents/GitHub/LeanModularForms && lake build 2>&1 | tail -10` — must end
   with `Build completed successfully`.
2. Axiom check via Lean LSP `lean_verify`:
   - `ForMathlib.valence_formula_textbook` → extra-axioms `[]`
   - `ForMathlib.hw_3_3_clean_full_mero` → extra-axioms `[]`
   - For Phase 2 only: also check `hw_3_3_clean_simple_mero`,
     `hw_3_3_clean_singlepole_mero`, `hw_3_3_clean_full_holo`, etc. — all 8 variants.
3. `#print` the signature of `hw_3_3_clean_full_mero` and verify byte-for-byte equal to
   the pre-phase-2 baseline. (Recommend: snapshot the signature in a comment block at
   the top of HW33Clean.lean before starting Phase 2.)
4. Commit and push with `LEAN4_GUARDRAILS_BYPASS=1 git push`.

---

## 5. What was already tried and why it failed

| Attempt | Date | Approach | Failure mode |
|---|---|---|---|
| P4a.1 (session) | 2026-05-21 | Add affine-reparam projection to `PiecewiseC1Path 0 1` | 198 refs, ~12K GRT proof lines use `γ.a/γ.b/∫γ.a..γ.b`; projection layer adds 100–150 lines for zero downstream simplification. Aborted clean. |
| P4c (session) | 2026-05-21 | Replace `fdBoundaryFun` with `Path.trans₅` assembly | `Path.trans` is dyadic (1/2 breakpoint), project uses 1/5. Custom 5-fold adds ~85 vs ~99 removable. Aborted clean. |
| P4a.2 (session) | 2026-05-21 | Restructure `ClosedPwC1Curve` to contain a `PiecewiseC1Path x x` | Agent stalled investigating `derivWithin_eq_deriv_on_Ioo` reuse. Working tree clean. |

All three were honest aborts. The common root cause: trying to do the unification
*without* first generalizing `PiecewiseC1Path` to accept arbitrary intervals.

---

## 6. Suggested entry point for a future session

Day 1 morning: read `Mathlib.Topology.Path` carefully. The key API to understand is
`Path.extend` and how it interacts with `Set.Icc.affineHomeomorph` /
`Set.Icc.iccHomeomorph`.

Day 1 afternoon: start Phase 1 by adding the new `PiecewiseC1Path a b hab x y` structure
*alongside* the existing one. Do not delete the existing one yet. Add the affine-reparam
isomorphism lemmas. Build green.

Day 2: complete Phase 1 by removing the `@[deprecated]` from the old type once all
existing call sites can route through the new free-interval form (with `a = 0, b = 1`).

Day 3: Phase 2 (`ClosedPwC1Curve` restructure). Snapshot HW33Clean.lean signatures
first.

Days 4–5: Phase 3 (PiecewiseC1Curve / GRT migration). The 13 files form a tight cluster.

Days 6–9: Phase 4 (FD segments) + buffer for axiom-check failures.

Day 10: final verification, PR description update, push.

---

*End of P4_PLAN.md.*
