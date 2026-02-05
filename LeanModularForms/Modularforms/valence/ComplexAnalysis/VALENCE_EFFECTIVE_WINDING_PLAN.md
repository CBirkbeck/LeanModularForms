# Effective Winding Number Plan (H-W 2.3 Context)

**Purpose:** define a long-term path that *formally proves* H-W Proposition 2.3 and uses it to justify effective winding numbers in the valence formula. A short-term fallback is included at the end.

This plan assumes the file split described in `VALENCE_SPLIT_PLAN.md`.

---

## 0) Key Clarification (Project Reality)

**H-W Prop 2.3 is NOT proved in `WindingNumberInterior.lean`.**

`WindingNumberInterior.lean` only proves **interior winding = 1** for points *off* the curve.  
It does **not** address crossings, so it cannot provide the H-W angle contribution formula.

Our current `cauchyPrincipalValue'` is defined by *symmetric* excision in the image:
```
lim_{ε→0+} ∫_{‖γ(t)-z0‖>ε} ...
```
This gives **0** at crossings (documented in `WindingNumber.lean`).  
Therefore, to formalize H-W, we must introduce **detour-based regularization** or an HW-specific winding definition.

---

## 1) What We Already Have

### `WindingNumber.lean`
- `angleAtCrossing` and `windingNumberWithAngles'` (angle-based contributions).
- Explicit warning that PV-based `generalizedWindingNumber'` gives 0 at crossings.
- Documented (but unfinished) H-W proof scaffolding.

### `BranchCutTracking.lean`
- Asymptotic ratio/argument lemmas (`ratio_asymptotic_single_crossing`, etc.).
- Discussion of sign/branch issues (core H-W difficulty).

### `ValenceFormula_Rect_Homotopy.lean`
- Interior winding = 1 via homotopy (to use for non-crossing points).

---

## 2) Target Statement from H-W (Proposition 2.3)

The H-W paper (Prop 3 / Eq. 16-17) states:

```
n_{z0}(Λ) = n_{z0}(Λ̃) + Σ_k α_k / (2π)
```

where:
- Λ is a closed piecewise C1 immersion that may pass through z0
- Λ̃ is the **detoured curve** that avoids z0 by inserting small clockwise arcs
- α_k is the angle contribution at each crossing

This is the correct long-term link between winding and angle contributions.

---

## 3) Formalization Plan for H-W 2.3 (Primary Path)

### Step 3.1 — Define the H-W generalized winding

**Definition (new):**
```
def generalizedWindingNumberHW (γ : PiecewiseC1Immersion) (z0 : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * limUnder (𝓝[>] 0) (fun ε => integral_detoured γ z0 ε)
```

where `integral_detoured` integrates `dz/(z-z0)` along the detoured curve Λ̃_ε.

**Helper definitions needed:**
1. `detourArc (z0 : ℂ) (r : ℝ) (θ₁ θ₂ : ℝ) : ℝ → ℂ`
2. `detourCurveSingle (γ) (t0) (ε) : PiecewiseC1Curve` (replace small interval with arc)
3. `detourCurve (γ) (crossings : Finset ℝ) (ε) : PiecewiseC1Curve`

**Lemma targets:**
```
detourCurve_continuous
detourCurve_closed
detourCurve_avoids
detourCurve_piecewiseC1
```

---

### Step 3.2 — Local crossing geometry

For each crossing t0, prove:
```
ratio_near_crossing_tendsto :
  (γ(t0-δ_L) - z0) / (γ(t0+δ_R) - z0) → -L_left / L_right
```
```
arg_ratio_mod_2pi :
  arg(-L_left / L_right) = arg(-L_left) - arg(L_right) (mod 2π)
```
```
angleAtCrossing_eq :
  angleAtCrossing γ t0 = arg(L_right) - arg(-L_left)
```
```
log_ratio_im_eq_angleAtCrossing :
  Im (log (-L_left / L_right)) = angleAtCrossing γ t0  (after branch selection)
```

**Already in repo (partial):**
- `ratio_asymptotic_single_crossing` (BranchCutTracking.lean)
- `log_ratio_im_eq_neg_angleAtCrossing` (WindingNumber.lean)

**Task:** finish the branch-selection lemma so the sign is correct (+angle, not −angle).

---

### Step 3.3 — Model sector / arc contribution

Use the existing lemma:
```
generalizedWindingNumber_modelSector'
```

Prove a bridge lemma:
```
detourArc_integral_eq_i_angle :
  lim_{ε→0} ∮_{detourArc} dz/(z-z0) = I * angleAtCrossing
```

The detour arc is a model sector; this should be a rewrite to the model sector lemma.

---

### Step 3.4 — Decompose the integral

Show, for each ε:
```
∮_Λ̃_ε dz/(z-z0) =
  ∮_Λ,|γ|>ε dz/(z-z0)  +  Σ (detourArc contributions)
```

**Helper lemmas:**
- `cauchyPrincipalValue_split` (WindingNumber.lean)
- intervalIntegral additivity on adjacent intervals
- local parametrization identity for detour arcs

---

### Step 3.5 — Conclude H-W 2.3

Finish:
```
hw_decomposition :
  generalizedWindingNumberHW γ z0
    = generalizedWindingNumber' detourCurve z0
      + windingNumberWithAngles' γ z0 crossings
```

For the FD boundary elliptic points, `detourCurve` avoids z0, hence the integer part is 0:
```
generalizedWindingNumberHW = windingNumberWithAngles'
```

---

## 4) Use H-W 2.3 in the Project

Once H-W 2.3 is formalized:

1. Define `effectiveWinding := generalizedWindingNumberHW`  
2. Prove `effectiveWinding_eq_windingNumberCoeff'` by case split  
3. Replace residue side lemma to use `effectiveWinding` (HW) instead of PV  
4. Keep the short-term definition only as a fallback

---

## 5) Backup Plan (short-term, only if HW stalls)

```
effectiveWinding(p) = 1/2 or 1/3 at elliptic points, PV interior otherwise
```
This still proves the valence formula, but does not justify the PV-angle link.

---

## 6) Work Order for AI (long-term path)

1. Implement `detourArc` + `detourCurveSingle` + `detourCurve` with regularity lemmas.  
2. Finish branch-selection lemmas in `BranchCutTracking.lean` / `WindingNumber.lean`.  
3. Prove `detourArc_integral_eq_i_angle` via `generalizedWindingNumber_modelSector'`.  
4. Prove the decomposition lemma `hw_decomposition`.  
5. Replace `effectiveWinding` with `generalizedWindingNumberHW`.  
6. Use this in the residue side and core identity.

---

## 7) Notes for AI workers

- Do **not** try to prove PV = angle for the current PV definition.  
  The symmetric cutoff yields 0 at crossings; this is a documented counterexample.  
- The H-W theorem requires a detoured (asymmetric) regularization.  
- Keep proofs small: isolate each arc computation, each local asymptotic, each split.
