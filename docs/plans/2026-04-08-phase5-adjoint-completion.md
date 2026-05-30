# Phase 5 Adjoint Theory — Completion Plan (2026-04-08)

## ⚠️ CRITICAL FINDING (2026-04-08 update)

The current `pet f g` definition in `PeterssonInnerProduct.lean` integrates over
`ModularGroup.fd` (the SL₂(ℤ) fundamental domain) regardless of the level Γ of the
cusp forms. This is **WRONG** for Γ = Γ₁(N) with N > 1.

**Why it's wrong:**
- For Γ ⊊ SL₂(ℤ), the Petersson inner product should integrate over a Γ-fundamental
  domain, not `fd`.
- `petersson(f,g)` is Γ₁(N)-periodic but NOT SL₂(ℤ)-periodic.
- The current `pet` is `1/[SL₂:Γ₁(N)] · ⟨f,g⟩_{Γ₁(N)}` if we're "lucky" — but actually
  it's not even that, because integrating a Γ-periodic function over an arbitrary
  SL₂(ℤ)-fundamental domain doesn't give a canonical answer.

**Impact on Phase 5 sorries:**
- `diamondOp_petersson_unitary` — **FALSE** with current `pet` (was "proved" but
  the proof relies on the false `peterssonInner_fd_eq_smul_fd` lemma; now reverted)
- `peterssonInner_fd_eq_smul_fd` — **FALSE for N > 1** (documented in code)
- `heckeT_p_adjoint`, `heckeT_n_adjoint` — questionable (depend on correct `pet`)
- `exists_simultaneous_eigenform_basis` — questionable

**Required fix:** Redefine `pet` for level-Γ₁(N) cusp forms as a coset-sum or
integral over a Γ₁(N)-fundamental domain. This is a major refactor affecting many files.

**Sorry-free results that ARE still valid:**
- `CuspForm.toModularForm'` — coercion (level-independent)
- `heckeT_p_zero_at_cusps`, `heckeT_n_cusp` — cuspidality preservation
  (level-independent, just structure)
- `smulInvariantMeasure_SL2R_hausdorff` — invariance of Hausdorff measure (correct)
- `heckeT_n_normal` — operator-level statement, doesn't depend on `pet`
- Jacobian helper lemmas — pure computations

## Original plan (with corrections)



## Goal
Complete the 6 remaining sorries in `LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean`.

## Reference findings

### Diamond–Shurman (DS)
- **§5.4 (p. 181-183)**: Petersson inner product definition. Hint 5.4.1(a) gives the differential forms approach to GL₂⁺(ℝ)-invariance.
- **§5.5 (p. 183+)**: Adjoints of Hecke Operators
  - **Prop 5.5.2**: `⟨f|[α], g⟩_{α⁻¹Γα} = ⟨f, g|[α']⟩_Γ` where `α' = det(α)α⁻¹` (the KEY change-of-variables identity)
  - **Thm 5.5.3**: `T_p* = ⟨p⟩⁻¹ T_p`, `⟨p⟩* = ⟨p⟩⁻¹` for `(p,N)=1`
  - **Thm 5.5.4**: `S_k(Γ₁(N))` has orthogonal basis of eigenforms
  - **Exercise 5.5.1**: For `(n,N)>1`, `T_n* = w T_n w⁻¹` (alternative formula)
- **§5.6 / Cor 5.6.3**: Old/new spaces have orthogonal bases of Hecke eigenforms

### Miyake
- **§1.4 (1.4.2)**: `dv(z) = dx dy / y²` defined; "**y⁻² dx dy is invariant under the action of SL₂(ℝ)**" — Miyake states this fact (line 1603)
- **§1.4 (1.4.3)**: `Im(αz) = det(α)/|j(α,z)|² · Im(z)`
- **§2.8 Thm 2.8.2**: General adjoint formula via `α' = det(α)α⁻¹`
- **§4.5 Thm 4.5.4**:
  1. `f|T*(n) = χ(n)(f|T(n))` if `(n,N)=1`
  2. `T(n)` and `T*(n)` are mutual adjoints
  3. `S_k(N,χ)` has basis of common eigenforms

## Critical path

```
SORRY 1 (Jacobian)
  └─→ SORRY 2 (fund domain) ─→ done diamondOp_petersson_unitary
  └─→ SORRY 3 (T_p adjoint via DS Prop 5.5.2)
        └─→ SORRY 4 (T_n adjoint)
              └─→ SORRY 5 (eigenform basis via spectral theorem)

SORRY 6 (Hausdorff identity) — ISOLATED, off critical path
```

## Sorry-by-sorry plan

### SORRY 1: `setLIntegral_smul_preimage_eq` ⭐ CRITICAL BLOCKER

**Statement:** `∫⁻ z in (g•·)⁻¹' s, y⁻² ∂(comap coe vol) = ∫⁻ z in s, y⁻² ∂(comap coe vol)` for `g ∈ SL(2,ℝ)`.

**Math (DS Hint 5.4.1(a)):**
- Differential forms: `dx ∧ dy = (i/2) dz ∧ dz̄`
- Möbius `αz = (az+b)/(cz+d)` has `d(αz) = dz/(cz+d)²` and `d(αz̄) = dz̄/(cz̄+d)²`
- So `d(αz) ∧ d(αz̄) = dz ∧ dz̄ / |cz+d|⁴`
- And `Im(αz)² = Im(z)²/|cz+d|⁴`
- Cancellation: `d(αz) ∧ d(αz̄) / Im(αz)² = dz ∧ dz̄ / Im(z)²` ✓

**Already proved (sorry-free helpers):**
- `hasDerivAt_mobius` — Möbius derivative
- `det_smul_one_eq_normSq` — real Jacobian = `|c|²`
- `im_smul_SL2_eq` — `Im(g•z) = Im(z)/normSq(cz+d)`
- `jacobian_density_cancel` — the algebraic cancellation

**Implementation steps:**
1. Define `f : ℂ → ENNReal := fun z => ENNReal.ofReal (z.im^(-2 : ℤ))`
2. Use the existing `MeasurePreserving coe (comap coe vol) (vol.restrict (range coe))` pattern from `hyperbolicMeasure_fd_lt_top` to transfer LHS → ℂ-integral
3. Same for RHS
4. Identify `coe '' ((g•·)⁻¹' s)` with `(Möbius g)⁻¹' (coe '' s) ∩ range coe` using `coe_specialLinearGroup_apply`
5. Apply `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` to the Möbius map on `coe '' s`
6. Use `jacobian_density_cancel` to simplify

**Difficulty:** HARD. ~80-100 line proof.

**Helper lemmas to prove:**
- `mobius_injOn_uhp`: Möbius is injective on `{z : ℂ | 0 < z.im}`
- `mobius_image_uhp`: `(Möbius g) '' {z | 0 < z.im} = {z | 0 < z.im}`
- `mobius_hasFDerivAt`: `HasFDerivAt (Möbius g) (some ℝ-linear map) z` for `z` in upper half plane

---

### SORRY 2: `peterssonInner_fd_eq_smul_fd`

**Statement:** `∫_{γ⁻¹·fd} petersson(f,g) dμ = ∫_{fd} petersson(f,g) dμ` for `γ ∈ SL(2,ℤ)`, `f, g ∈ S_k(Γ₁(N))`.

**Math (DS Exercise 5.4.4):**
- Both `fd` and `γ⁻¹·fd` are fundamental domains for SL₂(ℤ)
- `petersson(f,g)` is `Γ₁(N)`-periodic (by `petersson_smul`)
- For a `Γ₁(N)`-periodic function, `∫_{any SL₂(ℤ) fund. domain}` is the same value
- Reason: `[SL₂(ℤ):Γ₁(N)] · ∫_{fund. dom.} = ∫_{Γ₁(N)\ℍ}` (a constant)

**Status:** Partial proof in place — change of variables step is done (using `MeasurePreserving.setIntegral_image_emb`). Remaining: the equality `∫_{fd} petersson(f∣γ⁻¹, g∣γ⁻¹) dμ = ∫_{fd} petersson(f,g) dμ`.

**Implementation steps:**
1. Note that `f∣[k]γ⁻¹` is generally NOT equal to `f` for `γ⁻¹ ∉ Γ₁(N)`
2. Use the tiling argument: write `SL₂(ℤ) = ⊔ Γ₁(N) δᵢ`, decompose the integral
3. For each Γ₁(N)-coset, apply `Γ₁`-invariance of `petersson`
4. Combine to get equality of total integrals

**Alternative simpler route:** Use Mathlib's `IsFundamentalDomain` infrastructure if it exists for the modular group. Search for `ModularGroup.fd` `IsFundamentalDomain` properties.

**Difficulty:** HARD. Needs `IsFundamentalDomain` setup.

---

### SORRY 3: `heckeT_p_adjoint` — DS Thm 5.5.3

**Statement:** `pet (T_p f) g = pet f (⟨p⟩⁻¹ T_p g)` for `(p,N)=1`.

**Math (DS Prop 5.5.2 + Thm 5.5.3):**
1. **DS Prop 5.5.2(a)**: `⟨f|[α], g⟩_{α⁻¹Γα} = ⟨f, g|[α']⟩_Γ` for `α' = det(α)α⁻¹`
2. **DS Prop 5.5.2(b)**: For double cosets, `⟨f|[ΓαΓ], g⟩ = ⟨f, g|[Γα'Γ]⟩`
3. Apply (b) to `α = [[1,0],[0,p]]`: adjoint double coset has `α' = [[p,0],[0,1]]`
4. Matrix identity: `[Γ₁(N) [[p,0],[0,1]] Γ₁(N)]_k = ⟨p⟩⁻¹ T_p`
5. Combining: `T_p* = ⟨p⟩⁻¹ T_p`

**Helper lemmas needed:**
- `peterssonInner_slash_GL2plus`: DS Prop 5.5.2(a) for `α ∈ GL₂⁺(ℚ)`
- `peterssonInner_doubleCoset_adjoint`: DS Prop 5.5.2(b)
- `T_p_double_coset_adjoint_matrix`: The matrix identity for `[[p,0],[0,1]]`

**Implementation steps:**
1. Establish DS Prop 5.5.2(a) — uses Sorry 1 + change of variables for non-SL₂ matrices
2. Establish DS Prop 5.5.2(b) by linearity over coset representatives
3. Compute the matrix identity at the operator level (already have T_p decomposition)
4. Combine

**Difficulty:** VERY HARD. ~150-200 line proof. Probably best to break into multiple sub-lemmas.

---

### SORRY 4: `heckeT_n_adjoint`

**Statement:** `pet (T_n f) g = pet f (⟨n⟩⁻¹ T_n g)` for `(n,N)=1`.

**Math (Miyake Thm 4.5.4(1)):**
- Direct generalization of Sorry 3
- Miyake's proof: for `n` with `(n,N)=1`, decompose `T(n) = (n)^{k/2-1} Σ χ(α_v)(f|α_v)` and apply general adjoint formula

**Two routes:**
1. **Direct (Miyake)**: Same proof as Sorry 3 but for general n
2. **Via multiplicativity (DS)**: Use `T_{mn} = T_m T_n` for coprime, plus prime power recurrence

**Status:** Route 2 is BLOCKED on Phase 3 (Shimura 3.35). Route 1 requires the same machinery as Sorry 3.

**Implementation:** Once Sorry 3 is done, copy the proof pattern with `n` instead of `p`.

**Difficulty:** HARD (after Sorry 3).

---

### SORRY 5: `exists_simultaneous_eigenform_basis`

**Statement:** `∃ B : Finset (CuspForm), ...` (orthogonal basis of common Hecke eigenforms in `cuspFormCharSpace`).

**Math (DS Thm 5.5.4 / Miyake Thm 4.5.4(3)):**
- Apply spectral theorem for commuting normal operators on a finite-dimensional inner product space
- Hecke operators `{T_n, ⟨n⟩ : (n,N)=1}` are:
  - Commuting (proved: `heckeT_n_comm_diamondOp`, `heckeT_n_comm`)
  - Normal (P5-NOR done at the level of `T_n(⟨n⟩⁻¹ T_n)`)
- Need finite-dimensionality of `cuspFormCharSpace` (Phase 6 result?)

**Mathlib search needed:**
- `LinearMap.IsSymmetric.eigenvectorBasis` or similar
- Spectral theorem for commuting normal operators
- `DiagonalizableFamily` or `IsFamilyDiagonalizable`

**Difficulty:** HARD. Depends on Sorry 4 + Mathlib spectral theory.

---

### SORRY 6: `hyperbolicMeasure_eq_hausdorffMeasure` — ISOLATED

**Status:** Off the critical path. Not needed for any other sorry.

**Math:** Riemannian volume form identity. Needs Federer's area formula or geometric measure theory infrastructure not in Mathlib.

**Decision:** **SKIP for now.** Document as future work.

---

## Execution order

### Phase A (foundation)
1. **SORRY 1** — Jacobian computation. Most isolated, unblocks 2-5.
2. **SORRY 2** — Fundamental domain independence. Depends on 1.

### Phase B (adjoint formulas)
3. **SORRY 3** — `heckeT_p_adjoint` via DS Prop 5.5.2.
4. **SORRY 4** — `heckeT_n_adjoint` (similar to 3).

### Phase C (spectral theorem)
5. **SORRY 5** — Eigenform basis via Mathlib spectral theory.

### Skipped
6. **SORRY 6** — Decoupled, future work.

## Risk assessment

| Sorry | Risk | Mitigation |
|-------|------|------------|
| 1 (Jacobian) | Medium | All algebraic helpers proved. Need careful Mathlib API matching. |
| 2 (fund domain) | High | Tiling argument needs `IsFundamentalDomain` in Mathlib. May need custom infrastructure. |
| 3 (T_p adjoint) | Very High | DS Prop 5.5.2 is a substantial result. ~150-line proof. |
| 4 (T_n adjoint) | High | Once 3 is done, mostly mechanical generalization. |
| 5 (eigenform basis) | High | Mathlib's spectral theory may not have exactly what we need. |
| 6 | Very High | Skip — decoupled. |

## Next action

**START with SORRY 1** — the Jacobian computation. This is the foundation everything else builds on. All algebraic helpers are already proved sorry-free, so the remaining work is the measure-theoretic glue.
