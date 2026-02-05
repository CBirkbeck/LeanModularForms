# Valence Formula – Core Work Plan

**Scope for AI:** finish the remaining **core** sorries in the **split files**:
`ValenceFormula_ResidueSide.lean`, `ValenceFormula_ModularSide.lean`,
and `ValenceFormula_Core.lean`.

**Do NOT** work on PV or homotopy sorries here; those live in separate work files:
- Homotopy: `ValenceFormula_Rect_Homotopy.lean`
- PV: `ValenceFormula_PV_Work.lean`

**Target deliverables:**
- In `ValenceFormula_ResidueSide.lean`:
  - `pv_equals_residue_sum` (uses effective winding + residue theorem)
  - `effectiveWinding_eq_windingNumberCoeff'` (via boundary classification)
- In `ValenceFormula_ModularSide.lean`:
  - `pv_equals_modular_total` (wrapper around PV lemma)
- In `ValenceFormula_Core.lean`:
  - `valence_formula_base_identity` (already structured; should close once above are done)

---

## 0) Critical-path dependencies

You must assume the following external lemmas will be proven in their files:

**From homotopy file** (`ValenceFormula_InteriorWinding.lean`):
```
generalizedWindingNumber_fdBoundary_eq_one
```

**From PV file** (`ValenceFormula_PV.lean`):
```
pv_integral_eq_modular_transformation
pv_integral_exists_f'_over_f
```

If these are not available yet, leave **clear TODO markers** and proceed with the
rest of the core work that does not depend on them.

---

## 1) Boundary classification lemmas (B1–B3)

These are the main *core* obstacles in `effectiveWinding_eq_windingNumberCoeff'`.
Break them into **small helper lemmas** and solve them one at a time.

### 1.1 B1 – Zeros on arc are elliptic
**Current lemma (in file):**
```
lemma arc_zero_is_elliptic {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma 1) k)
    (p : UpperHalfPlane) (hp_in_D : p ∈ 𝒟') (hp_on_arc : ‖(p : ℂ)‖ = 1)
    (hp_zero : orderOfVanishingAt' f p ≠ 0) :
    p = ellipticPoint_i' ∨ p = ellipticPoint_rho' ∨ p = ellipticPoint_rho_plus_one
```

**Plan: split into helper lemmas**
1. **Geometry:** if `p ∈ 𝒟'` and `‖p‖ = 1`, then `p` lies on the unit-circle arc
   between `ρ' → i → ρ`. Use the explicit parameterization of the FD boundary arcs.
2. **Group symmetry:** for modular forms on SL2Z, if `p` is a zero, then so is `S·p = -1/p`.
   On the arc, `S·p` is the reflection across the imaginary axis; it equals `p` **only**
   at `i, ρ, ρ'`. Add helper:
   ```
   lemma on_arc_fixed_points_only
     (p : ℂ) (hp_arc : ‖p‖ = 1) (hp_re : |p.re| ≤ 1/2) :
     (p = I ∨ p = rho ∨ p = rho')
       ↔ (-1/p = p)
   ```
3. **Conclusion:** If `p` is a zero and `p ≠ i,ρ,ρ'`, then `p` and `S·p` are distinct
   zeros on the arc, contradicting the **orbifold property**. (If a direct contradiction
   is too heavy, see fallback below.)

**Fallback (if too hard):** weaken the lemma by adding a hypothesis that modular forms
have no boundary zeros except elliptic points. This keeps the valence formula correct
for the intended use and avoids deep orbifold theory.

---

### 1.2 B2 – Height cutoff (zeros have Im < H)
**Current lemma (in file):**
```
lemma zeros_below_height_cutoff {k : ℤ} (f : ModularForm (Gamma 1) k)
    (p : UpperHalfPlane) (hp_in_D : p ∈ 𝒟') (hp_zero : orderOfVanishingAt' f p ≠ 0) :
    (p : ℂ).im < Real.sqrt 3 / 2 + 1
```

**Plan:**
1. Use finiteness of zeros in a fundamental domain:
   - If a lemma exists in `Finiteness.lean` or `ValenceFormulaDefinitions.lean`, use it.
2. Use compactness of `𝒟' ∩ {z | im ≤ H}` to show all zeros are below some `H`.
3. Set `H = √3/2 + 1` and use the existing truncation in the file.

**Helper lemma skeleton:**
```
lemma zeros_im_bounded (f : ModularForm (Gamma 1) k) :
  ∃ H, ∀ p ∈ 𝒟', orderOfVanishingAt' f p ≠ 0 → (p : ℂ).im < H
```
Then specialize to `H_height`.

---

### 1.3 B3 – Vertical edge canonical representative
**Current lemma (in file):**
```
lemma vertical_edge_canonical {k : ℤ} (f : ModularForm (Gamma 1) k)
    (p : UpperHalfPlane) (hp_in_D : p ∈ 𝒟')
    (hp_on_edge : |(p : ℂ).re| = 1/2)
    (hp_ne_rho : p ≠ ellipticPoint_rho')
    (hp_ne_rho' : p ≠ ellipticPoint_rho_plus_one)
    (hp_zero : orderOfVanishingAt' f p ≠ 0) :
    False
```

**Plan:** break into two lemmas:
1. If `p` is on the right edge, then `p - 1` is on the left edge and has the same order
   (by T‑invariance). This uses `f(z+1) = f(z)`.
2. Show that the only *allowed* zero on vertical edges in `𝒟'` is `ρ` (left edge) or `ρ'`
   (right edge), and that `ρ'` is excluded by hypothesis.

**Helper lemma skeleton:**
```
lemma order_T_invariant {k : ℤ} (f : ModularForm (Gamma 1) k) (p : UpperHalfPlane) :
  orderOfVanishingAt' f (p + 1) = orderOfVanishingAt' f p
```
Then use it to contradict `hp_ne_rho` / `hp_ne_rho'`.

---

## 2) effectiveWinding vs windingNumberCoeff'

Once B1–B3 are proven, the lemma
```
effectiveWinding_eq_windingNumberCoeff'
```
should be straightforward:
- If `p = i` or `p = ρ`, `effectiveWinding` is by definition `1/2` or `1/3`.
- If not elliptic, B1/B2/B3 show `p` is interior, so `generalizedWindingNumber'` = 1
  (use `generalizedWindingNumber_fdBoundary_eq_one` from Rect Homotopy).

**Helper lemma to add (if helpful):**
```
lemma effectiveWinding_interior_eq_one
  (p : UpperHalfPlane) (hp_in_D : p ∈ 𝒟')
  (hp_not_i : p ≠ ellipticPoint_i') (hp_not_rho : p ≠ ellipticPoint_rho')
  (hp_not_rho' : p ≠ ellipticPoint_rho_plus_one)
  (hp_re : |(p:ℂ).re| < 1/2) (hp_norm : ‖(p:ℂ)‖ > 1) (hp_im : (p:ℂ).im < H_height) :
  effectiveWinding p = 1
```

---

## 3) pv_equals_residue_sum (core residue side)

**Current lemma (in file):**
```
lemma pv_equals_residue_sum ... :
  cauchyPrincipalValueOn ... = 2πi * ∑ p ∈ S, effectiveWinding p * residueSimplePole ...
```

**Plan (stepwise, use existing helpers):**
1. Define `S_int` and `S_ell` via `interiorPoints` / `ellipticPoints` (already in file).
2. Use `sum_split_interior_elliptic` to split the RHS sum.
3. On `S_int`, replace `effectiveWinding` by `generalizedWindingNumber'` using
   `effectiveWinding_interior`.
4. Apply `generalizedResidueTheorem'` to `S_int`:
   - Needs `pv_integral_exists_f'_over_f` (PV work).
   - Needs `hasSimplePoleAt_logDeriv_of_zero` (PV work).
   - Needs the curve `fundamentalDomainBoundaryImmersion` (already defined).
5. Add elliptic contributions by definition of `effectiveWinding` (1/2 at i, 1/3 at ρ).

**IMPORTANT:** do not use the old “PV = angle at elliptic points” lemma.
The PV-based winding is 0 at crossings. Use `effectiveWinding` only.

---

## 4) pv_equals_modular_total (core modular side)

This is **just** a wrapper around the PV lemma:
```
pv_integral_eq_modular_transformation
```
Once PV work is done, replace the sorry with:
```
exact pv_integral_eq_modular_transformation f ...
```

No new math should be added here.

---

## 5) Final assembly (already done)

`valence_formula_base_identity` is already structured correctly.
Once Sections 1–4 are done, the file should be sorry‑free.

---

## Reporting back (required)
When you return, include:
- Which lemmas you completed (by name),
- Any new helper lemmas you introduced,
- The **main blockers** still remaining (if any).

Keep proofs short. If a proof grows, split it into helper lemmas first.
