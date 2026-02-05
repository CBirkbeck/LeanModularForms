# Plan: Align `generalizedResidueTheorem'` with H‑W (GeneralizedResidueTheorem.tex)

Goal: compare our Lean statement/proof of the generalized residue theorem with the statement in
`GeneralizedResidueTheorem.tex` (Hungerbühler–Wasem), then **remove unnecessary hypotheses**
so the Lean theorem matches the paper as closely as possible. We will keep a two‑tier strategy:

- **Tier A (short‑term)**: keep any hypotheses needed by current mathlib lemmas (e.g. convex U),
  but *remove* assumptions that are *logically derivable* (e.g. PV existence for simple poles,
  continuity of principal part, closedness of finite sets). This tier is still stronger than H‑W
  but much closer.
- **Tier B (long‑term)**: drop convexity/“avoids” assumptions and replace them with
  **null‑homologous cycle in U** to exactly match H‑W’s Theorem 4 (thm‑residue). This likely
  needs new homology‑level infrastructure.

This file is a roadmap for refactoring **ResidueTheory.lean** and related PV lemmas.

---

## 0. Reference: H‑W theorem statement

From `GeneralizedResidueTheorem.tex`, Theorem **thm‑residue** (Section “A Generalized Residue Theorem”):

- **U** open in ℂ.
- **S** ⊂ U without accumulation points in U.
- **f : U \\ S → ℂ** holomorphic.
- **C** is a **null‑homologous immersed piecewise C¹ cycle in U**.
- **C contains only simple poles of f** (poles on C are order 1).

Then

```
PV (1/(2πi)) ∮_C f(z) dz = Σ_{s∈S} n_s(C) · res_s f.
```

For **higher order poles on C**, additional “flatness” + **angle condition** are required
(conditions (A) and (B) in the paper). We do **not** need that generality for the valence formula.

Key consequences:
- PV existence for simple poles on C is **proved**, not assumed.
- Only **piecewise C¹ immersion** is required (not C²).
- **Null‑homologous** is the replacement for convexity/contractible hypotheses.

---

## 1. Current Lean statement (ResidueTheory.lean)

`generalizedResidueTheorem'` currently assumes (abridged):

- `U` open **and convex** (`hU_convex`).
- `S` discrete + closed (`hS_discrete`, `hS_closed`).
- `S0 : Finset ℂ` for singularities on curve; `S0 ⊆ S`.
- `f` differentiable on `U \\ S0` (stronger than holomorphic).
- `γ : PiecewiseC1Immersion`, closed, image in U.
- `hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s`.
- `hf_ext : ∀ s ∈ S0, ContinuousAt (f - res/(z-s)) s`.
- **extra**: `hPV_singular : ∀ s∈S0, CauchyPrincipalValueExists' (res/(z-s)) ...`.

**Differences from H‑W** (potentially removable):

1. **Convex U** is not in H‑W (they use null‑homologous cycle).
2. **Closed S + discrete S** not required; H‑W uses “no accumulation points”.
3. **PV existence for each simple pole** is *proved* in H‑W, not assumed.
4. **hf_ext** should be derivable from `HasSimplePoleAt`.
5. `DifferentiableOn` could be weakened to `HolomorphicOn`/`AnalyticOn`.
6. `PiecewiseC1Immersion` may be overkill: we only need immersion at crossing points
   (where γ hits S0).

---

## 2. Concrete refactor target (Tier A)

### New target statement (finite‑set version)

We should replace the current theorem with a **finite‑set** statement closer to H‑W:

```
/-- Generalized residue theorem (finite set form, simple poles on the curve). -/
lemma generalizedResidueTheorem_finset
  (U : Set ℂ) (hU : IsOpen U)
  (S0 : Finset ℂ)
  (f : ℂ → ℂ)
  (hf : DifferentiableOn ℂ f (U \\ (S0 : Set ℂ)))
  (γ : PiecewiseC1Curve)  -- see immersion note below
  (hγ_closed : γ.IsClosed)
  (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ t ∈ U)
  (hS0_on_curve : ∀ t ∈ Icc γ.a γ.b, γ t ∈ S0 → ... )
  (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
  (hImm_on_S0 : ∀ t ∈ Icc γ.a γ.b, γ t ∈ S0 → deriv γ t ≠ 0) :
  CauchyPrincipalValueExistsOn S0 f γ ... ∧
  cauchyPrincipalValueOn S0 f γ ... =
    2πi * ∑ s∈S0, generalizedWindingNumber' γ ... s * residueSimplePole f s
```

Notes:
- Drop `S` entirely; the finite set `S0` is enough.
- Drop `hS_closed`, `hS_discrete`: Finset implies closed + discrete.
- `hf_ext` should be derived from `HasSimplePoleAt` (see helper lemma below).
- `hPV_singular` should be **proved** from `PiecewiseC1Immersion` + `HasSimplePoleAt`.

### Immersion requirement
H‑W requires **immersed** curve. We can replace `PiecewiseC1Immersion` by:

```
(hImm_on_S0 : ∀ t, γ t ∈ S0 → deriv γ t ≠ 0)
```

This is *strictly weaker* than full immersion and is sufficient for PV existence at crossings.
If this is hard, keep `PiecewiseC1Immersion` for now but **document** that it is stronger than H‑W.

---

## 3. Helper lemmas to remove extra hypotheses

### (A) Remove `hf_ext` assumption

Add lemma:

```
lemma hasSimplePoleAt_continuousAt_sub_residue
  (f : ℂ → ℂ) (s : ℂ) (h : HasSimplePoleAt f s) :
  ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s
```

This should be derivable from `HasSimplePoleAt` → `IsMeromorphic` decomposition.
Then delete `hf_ext` from the theorem and replace with this lemma.

### (B) Remove `hPV_singular`

Replace with lemma proved in PV‑work file:

```
lemma cauchyPrincipalValueExists_simplePole
  (γ : PiecewiseC1Curve) (hImm_on_S0 : ...) (s : ℂ)
  (hSimplePole : HasSimplePoleAt f s) :
  CauchyPrincipalValueExists' (fun z => residueSimplePole f s / (z - s)) γ a b s
```

This is the core PV infrastructure already being built in `ValenceFormula_PV_Work.lean`.
Once proved, remove the explicit hypothesis.

### (C) Avoid global `S` and its separation hypotheses

Since `S0` is a `Finset`, we can produce the separation and discreteness where needed:

```
lemma finset_separated (S0 : Finset ℂ) : ∃ δ > 0, ∀ s≠s' ∈ S0, δ ≤ ‖s'-s‖
```

or use existing finset compactness lemmas.

### (D) Replace `DifferentiableOn` with `HolomorphicOn`

If downstream lemmas accept holomorphic, use:

```
have hf : DifferentiableOn ℂ f (U \\ S0) := hf_holo.differentiableOn
```

This is mostly cosmetic but matches H‑W better.

---

## 4. Convexity vs null‑homologous (Tier B)

H‑W only assumes the cycle is **null‑homologous** in U, not that U is convex.
We currently use `integral_eq_sum_residues_of_avoids` which assumes convexity.

Plan to eventually replace:

- `hU_convex` with a lemma of the form:

```
lemma integral_eq_sum_residues_of_nullhomologous
  (U : Set ℂ) (hU : IsOpen U) (C : Cycle)
  (hC_null : NullHomologous C U) ... :
  ∮_C f = 2πi * Σ res
```

This likely requires **singular homology** or a dedicated “null‑homologous implies Cauchy theorem”
lemma. This is *long‑term*, not needed for valence formula.

For now: keep convex in Tier A, but document the gap.

---

## 5. C¹ vs immersion: match H‑W

- H‑W requires **piecewise C¹ immersion**.
- For our PV existence, we only need **nonzero derivative at crossings**.
- Plan: create a helper predicate:

```
def ImmersionOn (γ : ℝ → ℂ) (S0 : Set ℂ) := ∀ t, γ t ∈ S0 → deriv γ t ≠ 0
```

Then use `PiecewiseC1Curve` + `ImmersionOn` instead of `PiecewiseC1Immersion` in the theorem.
This matches H‑W more closely and weakens assumptions.

---

## 6. Step‑by‑step refactor instructions (AI‑friendly)

**Step 1 – Read H‑W statement**
- Locate `thm-residue` in `GeneralizedResidueTheorem.tex`.
- Note: assumptions are *open U*, *S without accumulation*, *null‑homologous immersed piecewise C¹ cycle*, *simple poles on C*.

**Step 2 – Add helper lemmas**
1. `hasSimplePoleAt_continuousAt_sub_residue`
2. `cauchyPrincipalValueExists_simplePole` (in PV work file)
3. `ImmersionOn` predicate to weaken immersion.

**Step 3 – Refactor generalizedResidueTheorem'**
- Create a new lemma `generalizedResidueTheorem_finset` with minimal assumptions.
- Replace uses of `hf_ext` and `hPV_singular` by the new helper lemmas.
- Keep convex U *temporarily* but move it to a note “not in H‑W; needed for current Cauchy theorem lemma”.

**Step 4 – Prove equivalence with old statement**
- Show old theorem implies new theorem (straightforward by instantiating extra hypotheses).
- Deprecate old theorem or mark it “stronger than H‑W”.

**Step 5 – (Long‑term) remove convexity**
- Add a TODO: replace `integral_eq_sum_residues_of_avoids` with null‑homologous version.
- This can be postponed; not needed for valence formula.

---

## 7. What not to do (avoid future wrong turns)

- Do **not** keep `hPV_singular` as an external hypothesis; H‑W proves PV existence for simple poles.
- Do **not** require `PiecewiseC1Immersion` if only needed at S0; weaken to “immersion on preimage of S0”.
- Do **not** attempt to prove H‑W’s higher‑order pole conditions unless needed later.

---

## 8. Deliverables checklist

- [ ] New lemma `hasSimplePoleAt_continuousAt_sub_residue`
- [ ] New lemma `cauchyPrincipalValueExists_simplePole`
- [ ] New `generalizedResidueTheorem_finset`
- [ ] Deprecate old `generalizedResidueTheorem'` or mark as stronger
- [ ] (Optional) new lemma: `integral_eq_sum_residues_of_nullhomologous`

---

## 9. Notes for the AI

When reporting progress, include:
- Which hypotheses were removed.
- Whether the lemma now matches H‑W exactly or still needs convexity.
- Any new helper lemmas introduced (with signatures).
- Whether any dependency (PV existence, ImmersionOn) is still missing.

---

## Appendix: Useful mathlib lemmas already available

These are not PV/winding lemmas, but they *do* replace classical residue‑theorem steps
when the integrand is holomorphic on a region (off a countable set). They’re useful to
avoid re‑proving Cauchy‑Goursat from scratch.

**Circle integrals**

- `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`
  - `circleIntegral.integral_sub_inv_of_mem_ball`:
    \n  ∮ (z − w)⁻¹ dz = 2πi when `‖w - c‖ < R`
  - `circleIntegral.integral_sub_zpow_of_ne` / `integral_sub_zpow_of_undef`
    for z‑powers with `n ≠ -1`

**Cauchy–Goursat on rectangles / annuli**

- `Mathlib/Analysis/Complex/CauchyIntegral.lean`
  - `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
  - `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`
  - `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`
  - `Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`

**Removable singularity tools**

- `Mathlib/Analysis/Complex/RemovableSingularity.lean`
  - `two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable`
  - Related lemmas that turn circle integrals into derivatives under differentiability

Use these in proofs where we *avoid* singularities (classical Cauchy), and keep
our PV machinery only for the singular‑on‑curve case.
