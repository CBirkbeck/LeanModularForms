# Plan: Hecke Eigenform Theory and Strong Multiplicity One

## Goal

Develop the **full theory of Hecke operators on modular forms** at mathlib quality,
culminating in the **Strong Multiplicity One Theorem** (Miyake Thm 4.6.12):

> Let f ∈ S_k^0(N, χ) and g ∈ S_k^1(N, χ). If f and g are common eigenfunctions
> of T(n) with the same eigenvalue for each n prime to some integer L, then
> g is a constant multiple of f.

**Important**: Diamond-Shurman Thm 5.8.2 only proves a weaker within-level result
and explicitly defers to [Miy89] for the full theorem. Our proof follows Miyake §4.6.

The plan develops the full theory comprehensively — eigenforms, Petersson inner product,
primitive forms, L-functions, Euler products — not just the minimum needed for SMO.

---

## Audit: What's Next for SMO (2026-04-17)

**Phases complete**: 1, 2, 3, 4 (all 0 sorries). Ring-hom refactor landed.

**Immediate next blockers for SMO** (in dependency order):

1. **Phase 5 (Adjoints)** — ACTIVE by other worker on `AdjointTheory.lean` (2 sorries).
   Key theorems needed: `heckeT_p_adjoint`, `heckeT_n_adjoint`, `heckeT_n_normal`,
   `simultaneous_eigenform_basis` (spectral theorem for commuting normal ops).

2. **Phase 6 (Primitive forms)** — MORE DEVELOPED than originally scoped.
   `Newforms.lean` (1725L) already contains:
   - `IsEigenform`, `Eigenform` struct (Miyake §4.5)
   - Level-raising infrastructure: `levelRaiseMatrix`, `levelRaiseConj`, `levelRaise`
     (Miyake Lemma 4.6.1)
   - `IsOldformGenerator`, `cuspFormsOld` (= Miyake's S_k^1)
   - `IsInNewSubspace`, `cuspFormsNew` (= Miyake's S_k^0)
   - `cuspFormsOld_disjoint_cuspFormsNew`
   - `cuspForm_finiteDimensional`
   - `petN_realBilin` + reflexivity
   - `cuspFormsOld_isCompl_cuspFormsNew` (the decomposition theorem!)
   - Hecke action on CuspForm + diamondOp_cusp + levelRaise commutation with Hecke
   - `Newform` API (newform_unique, exists_nonzero_prime_eigenvalue)

   **Remaining 2 sorries** are BOTH gated on OTHER tracks:
   - L1523: uses `heckeT_n_adjoint` + `exists_simultaneous_eigenform_basis` (AdjointTheory, Phase 5)
   - L1654: `exists_nonzero_prime_eigenvalue` (needs L-function theory, Phase 7)

   So Phase 6 is ~80% done; closing it requires Phase 5 completion + Phase 7 start.

3. **Phase 8 (Main Lemma)** — Miyake Thm 4.6.8 (~1000 LOC). Requires Phase 6 done.

4. **Phase 9 (SMO)** — Miyake Thm 4.6.12 (~400 LOC). Short proof given 6+8.

**Parallelizable now**: Phase 7 (L-functions) — independent of 5/6/8/9, builds on
completed Phase 3. Could be a worthwhile parallel track.

**Audit needed on Newforms.lean** (1725L, 2 sorries): is this already Miyake §4.6 work?
What specifically is in there? What's the gap to Miyake's complete framework?

## References

- **[DS]** Diamond-Shurman, *A First Course in Modular Forms*, Chapter 5
- **[Miy]** Miyake, *Modular Forms*, §4.5–4.6
- **[Shi]** Shimura, *Introduction to Arithmetic Theory of Automorphic Functions*, Chapter 3

## Existing Infrastructure

*Updated 2026-04-17 (major refactor complete)*

| Component | Status | Location |
|-----------|--------|----------|
| Abstract Hecke ring (𝕋, multiplication, associativity, commutativity) | ✅ | AbstractHeckeRing/ (8 files, 0 sorries) |
| GL₂ Hecke algebra (T(a,d), T(m), Shimura 3.24 identities) | ✅ | GL2/ (MultiplicationTable 1183L, etc.) |
| `heckeOperator`, `heckeOperatorLinear`, `heckeOperator_comp` | ✅ | GL2/HeckeModularForm.lean (562L) |
| **`heckeRingHom k : 𝕋 (GL_pair 2) ℤ →+* End(M_k(𝒮ℒ))`** | ✅ NEW | GL2/HeckeModularForm.lean |
| **`heckeRingHom_Gamma0 N k : 𝕋(Γ₀(N)) →+* End(M_k(Γ₀(N)))`** | ✅ NEW | GL2/HeckeModularForm_Gamma0.lean (391L) |
| Congruence subgroups Γ(N), Γ₀(N), Γ₁(N) with finite index | ✅ | Mathlib |
| **Hecke pair (Γ₁(N), Δ₁(N))** | ✅ | GL2/Gamma1Pair.lean (640L, 0 sorries) |
| **Hecke pair (Γ₀(N), Δ₀(N))** | ✅ | GLn/CongruenceHecke.lean |
| **Diamond operators ⟨d⟩ on M_k(Γ₁(N)) and S_k(Γ₁(N))** | ✅ | GL2/Gamma1Pair.lean |
| **Character-twisted slash action + IsNebentypus** | ✅ | GL2/Gamma1Pair.lean |
| **Nebentypus character spaces M_k(N,χ), S_k(N,χ)** | ✅ | GL2/Gamma1Pair.lean |
| **`M_k(Γ₁(N)) = ⊕_χ modFormCharSpace k χ`** (direct sum decomp) | ✅ NEW | GL2/CharacterDecomp.lean (339L) |
| **`modFormCharSpace k 1 ≃ M_k(Γ₀(N))`** (LinearEquiv) | ✅ NEW | GL2/CharSpaceIso.lean (236L) |
| **T_p on M_k(Γ₁(N)), comm with ⟨d⟩, preserves M_k(N,χ)** | ✅ | GL2/HeckeT_p.lean (1264L, 0 sorries) |
| **T_n on M_k(Γ₁(N)), comm, preserves M_k(N,χ)** | ✅ | GL2/HeckeT_n.lean (2541L, 0 sorries) |
| **Fourier coefficient formula for T_p, T_n + eigenform API** | ✅ | GL2/FourierHecke.lean (991L, 0 sorries) |
| **`heckeT_p_all_comm_distinct`** (T_p T_q = T_q T_p) | ✅ | GL2/HeckeT_n.lean:1071 |
| **Γ₁(N)↔Γ₀(N) Hecke bridge (D_p_Gamma1/D_p_Gamma0 + matching)** | ✅ NEW | GL2/HeckeT_p_Gamma1.lean (732L), GL2/HeckeT_p_Gamma0.lean (681L), GL2/HeckeT_p_Gamma0_Bridge.lean (435L) |
| **`heckeRingHomCharSpaceOne`: 𝕋(Γ₀(N)) →+* End(modFormCharSpace k 1)** | ✅ NEW | GL2/HeckeT_p_CharSpace_Comm.lean (281L) |
| **`heckeT_coprimeRestrict`**: T_n restricted to charSpace k χ (coprime monoid) | ✅ NEW | GL2/HeckeRingHomCharSpace_General.lean (245L) |
| **Prop 3.34 (Gamma0MapUnits preservation)**: coprime-det case | ✅ NEW | GL2/Prop334.lean (373L) |
| **Stabilizer surjectivity (diagonal case)** | ✅ NEW | GL2/Prop334_StabSurj.lean (298L) |
| **Level embedding f(z) ↦ f(lz)** | ✅ | GL2/LevelEmbed.lean (96L, 0 sorries) |
| **SL₂(ℤ) → SL₂(ℤ/dℤ) surjection** | ✅ | GLn/SL2Surjection.lean (244L, 0 sorries) |
| **Γ₀(N) Hecke pair + Shimura 3.35 surjection** | ✅ | GLn/CongruenceHecke.lean (6117L, 0 sorries) |
| Petersson inner product integrand + transformation law | ✅ | Mathlib (Petersson.lean) |
| **Petersson inner product (hyperbolic measure + integral)** | ✅ | Modularforms/PeterssonInnerProduct.lean (624L, 0 sorries) |
| **Eigenform / Newform / Primitive form infrastructure (partial)** | ⚠️ | GL2/Newforms.lean (1725L, 2 sorries) |
| **Hecke adjoint theory (active, other worker)** | ⚠️ | GL2/AdjointTheory.lean (2643L, 2 sorries) |
| Dirichlet characters + L-series infrastructure | ✅ | Mathlib |
| ModularForm / CuspForm / SlashInvariantForm types | ✅ | Mathlib |
| q-expansion / Fourier coefficient lemmas | ✅ | qExpansion_lems, FourierHecke |
| Old/new/primitive form decomposition (S_k^0/S_k^1) | ❌ | — |
| L-functions of eigenforms / Euler product | ❌ | — |

---

## Architecture: 9 Phases

*Updated 2026-04-17: major refactor landed; Phases 1-4 now complete.*

```
Phase 1: Hecke pair for Γ₁(N)          ✅ COMPLETE (GL2/Gamma1Pair.lean, 640L, 0 sorries)
Phase 2: Diamond operators + T_p        ✅ COMPLETE (HeckeT_p.lean 1264L, 0 sorries)
Phase 3: T_n and Fourier coefficients   ✅ COMPLETE (HeckeT_n 2541L + FourierHecke 991L, 0 sorries)
Phase 4: Petersson inner product         ✅ COMPLETE (4 files, ~1520L, 0 sorries)
Phase 5: Adjoint theory                  ⚠️ ACTIVE (AdjointTheory.lean 2643L, 2 sorries — other worker)
Phase 6: Primitive form theory           ⚠️ PARTIAL (Newforms.lean 1725L, 2 sorries)
Phase 7: L-functions and Euler products  ❌ NOT STARTED (needs Phase 3 — now unblocked)
Phase 8: Main Lemma (decomposition)      ❌ NOT STARTED (needs Phase 6)
Phase 9: Strong Multiplicity One         ❌ NOT STARTED (needs Phases 6+8)
```

**Note on file consolidation**: The plan originally expected separate files for
Gamma0Pair, DiamondOperator, CharacterDecomposition, etc. In practice, Phases 1-2
were consolidated into `Gamma1Pair.lean` (diamond ops, character spaces, Nebentypus,
bridge theorems) and `HeckeT_p.lean` (T_p definition, commutativity, character
preservation). Phase 3 expanded beyond expectations into `HeckeT_n.lean` (2541L)
and `FourierHecke.lean` (991L). This is cleaner than the original file split.

**2026-04-17 refactor additions** (ring-hom infrastructure, ~4500 LOC):

| New file | LOC | Purpose |
|---|---|---|
| GL2/HeckeModularForm_Gamma0.lean | 391 | `heckeRingHom_Gamma0 N k` |
| GL2/CharacterDecomp.lean | 339 | `M_k(Γ₁(N)) = ⊕_χ modFormCharSpace k χ` |
| GL2/CharSpaceIso.lean | 236 | `modFormCharSpace k 1 ≃ M_k(Γ₀(N))` |
| GL2/HeckeT_p_Gamma0.lean | 681 | `D_p_Gamma0` + cardinality + coset-reps Equiv |
| GL2/HeckeT_p_Gamma0_Bridge.lean | 435 | Trivial-χ bridge `heckeSlash_gen = heckeT_p_fun` |
| GL2/HeckeT_p_CharSpace_Comm.lean | 281 | `heckeRingHomCharSpaceOne` (trivial χ) |
| GL2/HeckeRingHomCharSpace.lean | 288 | `heckeT_p_all_charRestrict` + commutativity |
| GL2/HeckeRingHomCharSpace_General.lean | 245 | `heckeT_coprimeRestrict` (coprime monoid) |
| GL2/Prop334.lean | 373 | Shimura 3.34: Gamma0MapUnits preserved under conjugation |
| GL2/Prop334_StabSurj.lean | 298 | Stabilizer surjectivity (diagonal case) |
| GL2/Prop334_HeckeSlash.lean | 283 | Wrapping infrastructure (given hComm) |
| GL2/Prop334_HeckeSlashDiag.lean | 207 | χ-equivariance of heckeT_p_fun (trivial-χ target) |
| GL2/HeckeSlashExplicit.lean | 273 | Explicit slash via Shimura/DS coset reps |

Plus `Gamma1Pair.lean`, `HeckeT_p_Gamma1.lean`, `HeckeT_p_GLpair.lean` expanded during session.

---

## Phase 1: Hecke Pair for Γ₁(N) — ✅ COMPLETE

**Goal**: Define a `HeckePair` with `H = Γ₁(N)` and connect it to our abstract Hecke ring.

**Status**: COMPLETE — `GL2/Gamma1Pair.lean` (634 lines, 0 sorries). All definitions,
lemmas, and the `Gamma1_pair` constructor are proven. File also includes Phase 2 content
(diamond operators, character spaces, Nebentypus).

**Reference**: [Miy] §4.5 (Thm 4.5.18), [DS] §5.1

### Why This Is Needed

Our current `GL_pair 2` has `H = SL₂(ℤ)`. For the eigenform theory we need level structure:
Hecke operators on `M_k(Γ₁(N))` that respect the Nebentypus character χ. This requires
a new Hecke pair where `H = Γ₁(N)` and `Δ = Δ₁(N)`.

### Definitions

```lean
/-- Δ₁(N): integer matrices with a ≡ 1 (mod N), c ≡ 0 (mod N), positive determinant. -/
def Delta1 (N : ℕ) : Submonoid (GL (Fin 2) ℚ)

/-- The Hecke pair (Γ₁(N), Δ₁(N)) for level N. -/
noncomputable def Gamma1_pair (N : ℕ) : HeckePair (GL (Fin 2) ℚ) where
  H := Gamma1 N  -- embedded in GL₂(ℚ) via mapGL
  Δ := Delta1 N
  h₀ := Gamma1_le_Delta1 N
  h₁ := Delta1_le_commensurator_Gamma1 N

/-- The Hecke pair (Γ₀(N), Δ₀(N)) for level N. -/
noncomputable def Gamma0_pair (N : ℕ) : HeckePair (GL (Fin 2) ℚ)
```

### Key Lemmas

1. `Gamma1_le_Delta1`: Γ₁(N) ≤ Δ₁(N)
2. `Delta1_le_commensurator_Gamma1`: Δ₁(N) ≤ commensurator(Γ₁(N))
3. `Hecke_algebra_Gamma1_comm`: The Hecke algebra R(Γ₁(N), Δ₁(N)) is commutative
   — [Miy] Thm 4.5.3, proved via the transpose anti-involution (already done for GL_pair)
4. `Hecke_algebra_isomorphism`: R(Γ₁(N), Δ₁(N)) ≅ R(Γ₀(N), Δ₀(N)) — [Miy] Thm 4.5.18
5. `Gamma1_Gamma0_correspondence`: The correspondence Γ₁(N)αΓ₁(N) ↦ Γ₀(N)αΓ₀(N) is
   well-defined and an isomorphism of Hecke algebras

### Files

- `GL2/Gamma1Pair.lean` — Δ₁(N) definition and Hecke pair
- `GL2/Gamma0Pair.lean` — Δ₀(N) definition and Hecke pair
- `GL2/HeckeAlgebraLevel.lean` — isomorphism between level-N Hecke algebras

---

## Phase 2: Diamond Operators, Twisted Slash, and T_p — ✅ COMPLETE

**Goal**: Define ⟨d⟩ and T_p as concrete endomorphisms of `M_k(Γ₁(N))`, and make
Nebentypus a first-class transformation-law notion via a character-twisted slash action
on `Γ₀(N)`.

**Status** (updated 2026-04-17): **COMPLETE**. All 8 previous sorries in `HeckeT_p.lean`
are now filled. File is 1264 lines, 0 sorries. Diamond operators, character spaces,
Nebentypus, and bridge theorems are in `GL2/Gamma1Pair.lean` (640L, 0 sorries).

**Reference**: [DS] §5.2, [Miy] §4.5

### Definitions

```lean
/-- Character-twisted slash action on `Γ₀(N)`.
    Fixed points satisfy the classical Nebentypus relation `f |[k] g = χ(g) • f`. -/
noncomputable def twistedSlash (N : ℕ) (k : ℤ)
    (χΓ : Gamma0 N →* ℂˣ) (g : Gamma0 N) (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ

/-- Function-level Nebentypus invariance on `Γ₀(N)`. -/
def IsNebentypus (N : ℕ) (k : ℤ) (χΓ : Gamma0 N →* ℂˣ)
    (f : UpperHalfPlane → ℂ) : Prop

/-- The diamond operator ⟨d⟩ for d ∈ (ℤ/Nℤ)*.
    Action: ⟨d⟩f = f|[α]_k where α = [a b; cN d'] ∈ Γ₀(N) with d' ≡ d (mod N). -/
noncomputable def diamondOp (N : ℕ) (d : (ZMod N)ˣ) (k : ℤ) :
    ModularForm (Gamma1 N) k →ₗ[ℂ] ModularForm (Gamma1 N) k

/-- T_p for prime p, as a double coset operator.
    T_p = [Γ₁(N) [1 0; 0 p] Γ₁(N)]_k -/
noncomputable def heckeT_p (N : ℕ) (p : ℕ) (hp : p.Prime) (k : ℤ) :
    ModularForm (Gamma1 N) k →ₗ[ℂ] ModularForm (Gamma1 N) k

/-- The derived character eigenspace view
    `M_k(N, χ) = {f ∈ M_k(Γ₁(N)) : ⟨d⟩f = χ(d)f ∀ d}`. -/
def ModularFormCharSpace (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) :
    Submodule ℂ (ModularForm (Gamma1 N) k)
```

### Architecture Choice

The primary character-facing API should be the twisted slash action on `Γ₀(N)`, not
the `Γ₁(N)` diamond-eigenspace package. The eigenspace view remains important, but as a
bridge theorem:

- twisted-slash invariance on `Γ₀(N)` restricts to an ordinary modular form on `Γ₁(N)`;
- the image is exactly the corresponding diamond-operator eigenspace;
- trivial character recovers the ordinary `Γ₀(N)` slash law.

This avoids making character forms look like a secondary spectral decomposition artifact
and keeps future bundled with-character structures aligned with mathlib’s existing
`extends SlashInvariantForm` packaging.

### Key Theorems

1. `diamondOp_well_defined`: Independent of choice of lift α ∈ Γ₀(N)
2. `diamondOp_mul`: ⟨d⟩⟨e⟩ = ⟨de⟩ — [DS] Prop 5.2.4(b)
3. `twistedSlash_one` / `twistedSlash_mul`: the twisted slash is an action
4. `isNebentypus_iff`: fixed points satisfy the classical relation `f |[k] g = χ(g) • f`
5. `trivialCharacter_nebentypus_iff`: trivial character recovers ordinary `Γ₀(N)` slash invariance
6. `modFormCharSpace_iff_nebentypus` / `cuspFormCharSpace_iff_nebentypus`:
   bridge between twisted-slash invariance and the current `Γ₁(N)` eigenspace view
7. `diamondOp_comm_heckeT_p`: ⟨d⟩T_p = T_p⟨d⟩ — [DS] Prop 5.2.4(a)
8. `heckeT_p_comm`: T_p T_q = T_q T_p for distinct primes p, q — [DS] Prop 5.2.4(c)
9. `ModularForm_char_decomp`: M_k(Γ₁(N)) = ⊕_χ M_k(N, χ) — the χ-eigenspace decomposition
10. `heckeT_p_preserves_char`: T_p maps M_k(N, χ) to itself — [DS] Prop 5.2.2(b)
11. `heckeT_p_preserves_cusp`: T_p maps S_k(Γ₁(N)) to itself
12. `heckeT_p_explicit`: Explicit orbit formula — [DS] Prop 5.2.1:
   - p | N: T_p f = Σ_{j=0}^{p-1} f|[[1 j; 0 p]]_k
   - p ∤ N: T_p f = Σ_{j=0}^{p-1} f|[[1 j; 0 p]]_k + f|[[m n; N p][p 0; 0 1]]_k

### Connection to Abstract Hecke Ring

`heckeT_p` is the specialization of our abstract `heckeOperator` to the `Gamma1_pair N`
Hecke pair, applied to the double coset of `[1 0; 0 p]`. The bridge:

```lean
/-- T_p on M_k(Γ₁(N)) equals the abstract Hecke operator for the coset ⟦[1 0; 0 p]⟧. -/
theorem heckeT_p_eq_heckeOperator (N : ℕ) (p : ℕ) (hp : p.Prime) (k : ℤ) :
    heckeT_p N p hp k = heckeOperator k (⟦diag_matrix_in_Delta1 N p⟧ : HeckeCoset (Gamma1_pair N))
```

### Files (ACTUAL, post-consolidation)

<!-- Original split (obsolete): separate DiamondOperator.lean + CharacterDecomposition.lean.
     Actual landing: diamond ops + char spaces consolidated into Gamma1Pair.lean;
     direct-sum decomposition implemented as CharacterDecomp.lean via mathlib
     joint-eigenspace semisimplicity. -->

- `GL2/Gamma1Pair.lean` (640L) — ⟨d⟩ definition, multiplicativity, char spaces, Nebentypus
- `GL2/HeckeT_p.lean` (1264L) — T_p definition, explicit formula, character preservation
- `GL2/CharacterDecomp.lean` (339L, NEW 2026-04-17) — `M_k(Γ₁(N)) = ⊕_χ charSpace k χ`
- `GL2/CharSpaceIso.lean` (236L, NEW 2026-04-17) — `modFormCharSpace k 1 ≃ M_k(Γ₀(N))`

---

## Phase 3: T_n and Fourier Coefficient Formula — ✅ COMPLETE

**Goal**: Define T_n for all n, prove the Fourier coefficient formula, and establish
that eigenvalues equal Fourier coefficients for normalized eigenforms.

**Status** (updated 2026-04-17): **COMPLETE**.

| File | Lines | Sorries | Content |
|------|-------|---------|---------|
| `GL2/HeckeT_n.lean` | 2541 | 0 | T_n definition, recurrence, multiplicativity, commutativity, char preservation |
| `GL2/FourierHecke.lean` | 991 | 0 | Fourier coefficient formulas, eigenform API, eigenvalue=coefficient theorem |

<!-- Obsolete: the 10 sorries listed here (matrix equations, termination, coprime bridge,
     fourierCoeff_heckeT_p) are all resolved. `heckeT_p_all_comm_distinct` (HeckeT_n.lean:1071)
     and `heckeT_n_comm` (HeckeT_n.lean:1681) are both proved. -->

**Reference**: [DS] §5.3, [Miy] §4.5 (Thm 4.5.13, Lemma 4.5.14–15, Thm 4.5.16)

### Definitions

```lean
/-- T_n for general n ∈ ℤ⁺. Defined by:
    T_1 = 1, T_{p^r} = T_p T_{p^{r-1}} - p^{k-1} ⟨p⟩ T_{p^{r-2}} (r ≥ 2),
    T_{mn} = T_m T_n when (m,n) = 1. -/
noncomputable def heckeT_n (N : ℕ) (n : ℕ+) (k : ℤ) :
    ModularForm (Gamma1 N) k →ₗ[ℂ] ModularForm (Gamma1 N) k

/-- ⟨n⟩ extended to all n ∈ ℤ⁺ (= 0 when (n,N) > 1). -/
noncomputable def diamondOp_n (N : ℕ) (n : ℕ+) (k : ℤ) :
    ModularForm (Gamma1 N) k →ₗ[ℂ] ModularForm (Gamma1 N) k
```

### Key Theorems

1. **`heckeT_n_recurrence`**: T_{p^r} = T_p T_{p^{r-1}} - p^{k-1}⟨p⟩T_{p^{r-2}} — [DS] (5.10)
2. **`heckeT_n_multiplicative`**: T_{mn} = T_m T_n when (m,n) = 1
3. **`fourierCoeff_heckeT_p`** (THE key formula): — [DS] Prop 5.2.2, [Miy] Lemma 4.5.14
   For f ∈ M_k(N, χ):
   ```
   a_n(T_p f) = a_{np}(f) + χ(p) p^{k-1} a_{n/p}(f)
   ```
4. **`fourierCoeff_heckeT_n`** (general formula): — [DS] Prop 5.3.1, [Miy] Thm 4.5.13
   For f ∈ M_k(N, χ):
   ```
   a_m(T_n f) = Σ_{d | (m,n)} χ(d) d^{k-1} a_{mn/d²}(f)
   ```
5. **`heckeT_mn_fourier`**: The multiplicativity formula — [Miy] Thm 4.5.13:
   ```
   t(m)t(n) = Σ_{d | (m,n)} χ(d) d^{k-1} t(mn/d²)
   ```
6. **`eigenvalue_eq_fourierCoeff`**: — [Miy] Thm 4.5.16, [DS] (5.21)
   If f ∈ G_k(N, χ) is a common eigenfunction of all T(n) with (n,N) = 1 and a₁(f) ≠ 0:
   - f|T(n) = t(n)f implies t(n) = a_n(f)/a₁(f)
   - If normalized (a₁ = 1): t(n) = a_n(f)
7. **`eigenvalue_multiplicative`**: — [Miy] Lemma 4.5.15
   The eigenvalues satisfy t(m)·c(n) = c(mn) and thus t(m)t(n) = Σ χ(d)d^{k-1}t(mn/d²)

### Files

- `GL2/HeckeT_n.lean` — T_n definition, recurrence, multiplicativity
- `GL2/FourierHecke.lean` — Fourier coefficient formula for T_p and T_n
- `GL2/EigenvalueCoefficient.lean` — eigenvalue = Fourier coefficient theorem

---

## Phase 4: Petersson Inner Product — ⚠️ 50% (PeterssonInnerProduct.lean exists)

**Goal**: Define ⟨f,g⟩_Γ as an actual integral, prove convergence, establish inner product
space structure on S_k(Γ). **No axiomatization — full convergence proof.**

**Status** (updated 2026-04-10): **✅ COMPLETE** for the critical path to SMO.

Four files, ~1520 lines total, **0 sorries**:

| File | Lines | Key results |
|------|-------|-------------|
| `PeterssonInnerProduct.lean` | 624 | μ_hyp, integrability, boundary null, fd=fdo ae |
| `PeterssonInner.lean` | 122 | Inner ℂ instance, pet_definite (identity theorem) |
| `PeterssonLevelN.lean` | 397 | petN (level-N inner product), positive-definiteness, Hermitian symmetry, sesquilinearity, diamond unitarity |
| `PSL2Action.lean` | 418 | PSL₂ action, SMulInvariantMeasure, IsFundamentalDomain, Möbius HasDerivAt, density-Jacobian identity |

**Proved theorems** (all axiom-clean):
- `petN_definite` — positive-definiteness
- `petN_conj_symm` — Hermitian symmetry
- `petN_add_right/left` — additivity
- `petN_smul_right`, `petN_conj_smul_left` — complex sesquilinearity
- `petN_neg_right/left` — negation
- `petN_slash_invariant` — **diamond unitarity** `petN(f∣γ)(g∣γ) = petN f g`
- `instSMulInvMeasure_SL/PSL` — `SMulInvariantMeasure SL₂/PSL₂ ℍ μ_hyp`
- `isFundamentalDomain_fdo_PSL` — `IsFundamentalDomain PSL₂ fdo μ_hyp`
- `density_jacobian_identity` — `im(τ)⁻² = im(gτ)⁻² · normSq(denom)⁻²`
- `integrableOn_petersson_slash` — integrability of slashed cusp forms

**Remaining nice-to-haves** (not blocking Phase 5+):
- Level compatibility `⟨f,g⟩_{Γ'} = ⟨f,g⟩_Γ` ([DS] Ex 5.4.3)
- Volume formula `V_{SL₂} = π/3`
- Eisenstein orthogonality ([DS] §5.11)

**Reference**: [DS] §5.4, [Miy] §2.7–2.8

### Definitions

```lean
/-- The hyperbolic measure dμ(τ) = dx dy / y² on ℍ. -/
def hyperbolicMeasure : MeasureTheory.Measure UpperHalfPlane

/-- The Petersson inner product on cusp forms.
    ⟨f,g⟩_Γ = (1/V_Γ) ∫_{X(Γ)} f(τ) conj(g(τ)) Im(τ)^k dμ(τ) -/
noncomputable def peterssonInnerProduct (Γ : Subgroup SL(2,ℤ)) (k : ℤ)
    (f g : CuspForm Γ k) : ℂ

/-- Inner product space instance on CuspForm Γ k. -/
noncomputable instance : Inner ℂ (CuspForm Γ k)
```

### Convergence Proof Strategy

The convergence requires showing the integral is finite. The key ingredients:

1. **Cusp form decay**: f(τ) = O(e^{-2πy}) as y → ∞ — from the q-expansion with a₀ = 0
2. **Integrand bound**: |f(τ)g̅(τ)| y^k ≤ C·e^{-4πy} on the fundamental domain
3. **Fundamental domain**: X(Γ) = Γ\ℍ has finite hyperbolic area V_Γ
4. **Dominated convergence**: The integral over X(Γ) converges by comparison with ∫ e^{-4πy} y^{k-2} dy

Mathlib already has:
- `petersson_exp_decay_left/right` — exponential decay for cusp forms
- `petersson_isZeroAtImInfty` — vanishing at infinity
- The transformation law `petersson_slash_SL`
- `ModularGroup.fd` / `ModularGroup.fdo` — the standard modular fundamental domains
- `ModularGroup.exists_smul_mem_fd` — the reduction theorem into `𝒟`
- `ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo` — uniqueness on `𝒟ᵒ`

What we need to build:
- Integration over Γ\ℍ using a fundamental domain
- The bridge from the existing modular-domain API to the exact measure-theory interface we need;
  do not rebuild the standard-domain reduction algorithm from scratch
- The volume V_Γ = [SL₂(ℤ) : ±Γ] · V_{SL₂(ℤ)}
- Absolute convergence via the decay estimates

### Key Properties

1. `peterssonInnerProduct_linear_left`: Sesquilinear (linear in first, conjugate-linear in second)
2. `peterssonInnerProduct_conj_symm`: ⟨f,g⟩ = conj(⟨g,f⟩)
3. `peterssonInnerProduct_pos_def`: ⟨f,f⟩ > 0 for f ≠ 0
4. `peterssonInnerProduct_level_compat`: ⟨f,g⟩_{Γ'} = ⟨f,g⟩_Γ for Γ' ⊂ Γ — [DS] Ex 5.4.3
5. `eisenstein_orthogonal_cusp`: ⟨E,f⟩ = 0 for Eisenstein E, cusp form f — [DS] §5.11

### Files

- `Modularforms/HyperbolicMeasure.lean` — dμ = dx dy/y², invariance
- `Modularforms/FundamentalDomain.lean` — Integration over Γ\ℍ, volume
- `Modularforms/PeterssonInner.lean` — Inner product, convergence, properties

---

## Phase 5: Adjoint Theory and Eigenform Diagonalization — ⚠️ ACTIVE (other worker)

**Goal**: Compute adjoints of Hecke operators w.r.t. Petersson, prove normality,
apply spectral theorem for simultaneous diagonalization.

**Status** (2026-04-17): Active work by another agent. `GL2/AdjointTheory.lean` is
2643L with 2 remaining sorries. Active commits include T205-a, T205-d helpers,
peterssonInner_add_left, sum_setIntegral_GL2_shift, and right-slash adjoint variants.

**Reference**: [DS] §5.5, [Miy] §4.5 (Thm 4.5.4–4.5.5)

### Key Theorems

1. **`heckeT_p_adjoint`**: T_p* = ⟨p⟩⁻¹ T_p — [DS] Thm 5.5.3, [Miy] Thm 4.5.4
   (Proof uses Prop 5.5.2: ⟨f|[α], g⟩ = ⟨f, g|[α']⟩ where α' = det(α)α⁻¹)
2. **`diamondOp_adjoint`**: ⟨p⟩* = ⟨p⟩⁻¹ — [DS] Thm 5.5.3
3. **`heckeT_n_adjoint`**: For (n,N) = 1: T_n* = ⟨n⟩⁻¹ T_n — [Miy] Thm 4.5.5
4. **`heckeT_n_normal`**: T_n T_n* = T_n* T_n for (n,N) = 1
5. **`simultaneous_eigenform_basis`**: S_k(Γ₁(N)) has an orthogonal basis of simultaneous
   eigenforms for {T_n, ⟨n⟩ : (n,N) = 1} — [DS] Thm 5.5.4

### Eigenform API

```lean
/-- Predicate: f is a Hecke eigenform (eigenfunction of all T_n, ⟨n⟩ with (n,N)=1). -/
def IsHeckeEigenform (N : ℕ) (k : ℤ) (f : ModularForm (Gamma1 N) k) : Prop :=
  ∀ n : ℕ+, n.val.Coprime N → ∃ λ : ℂ, heckeT_n N n k f = λ • f

/-- Predicate: f is a normalized eigenform (a₁ = 1). -/
def IsNormalizedEigenform (N : ℕ) (k : ℤ) (f : ModularForm (Gamma1 N) k) : Prop :=
  IsHeckeEigenform N k f ∧ fourierCoeff f 1 = 1

/-- The eigenvalue system of an eigenform. -/
noncomputable def eigenvalueSystem (N : ℕ) (k : ℤ)
    (f : ModularForm (Gamma1 N) k) (hf : IsHeckeEigenform N k f) :
    {n : ℕ+ // n.val.Coprime N} → ℂ

/-- The Dirichlet character associated to an eigenform via ⟨d⟩f = χ(d)f. -/
noncomputable def eigenformChar (N : ℕ) (k : ℤ)
    (f : ModularForm (Gamma1 N) k) (hf : IsHeckeEigenform N k f) :
    DirichletCharacter ℂ N
```

### Spectral Theorem Application

The diagonalization uses:
- S_k(Γ₁(N)) is finite-dimensional (from dimension formulas, in Mathlib)
- {T_n : (n,N) = 1} is a commuting family of normal operators
- Spectral theorem: commuting normal operators on a finite-dimensional inner product space
  are simultaneously diagonalizable

Mathlib has `LinearMap.IsSymmetric.eigenvectorBasis` for symmetric operators.
For normal operators we may need: `Module.End.eigenspace` + simultaneous version.

### Files

- `GL2/HeckeAdjoint.lean` — Adjoint computation: T_p* = ⟨p⟩⁻¹T_p
- `Eigenforms/Basic.lean` — IsHeckeEigenform, IsNormalizedEigenform predicates
- `Eigenforms/Diagonalization.lean` — Spectral theorem → eigenform basis

---

## Phase 6: Primitive Form Theory (Miyake's Approach) — ⚠️ PARTIAL

**Goal**: Develop the full theory of primitive forms following Miyake §4.6. This is
more general than Diamond-Shurman's old/new framework and is what's needed for
the full Strong Multiplicity One.

**Status** (2026-04-17): `GL2/Newforms.lean` exists at 1725L with 2 remaining sorries.
Substantial infrastructure for eigenforms and primitive forms already written.
`GL2/LevelEmbed.lean` (96L, 0 sorries) provides f(z) ↦ f(lz) (Miyake Lemma 4.6.1).

**Reference**: [Miy] §4.6 (Lemma 4.6.1–Thm 4.6.16)

### Key Definitions (Miyake's Framework)

Miyake works with the spaces:
- G_k(N, χ) = modular forms of weight k, level N, character χ
- S_k(N, χ) = cusp forms therein

**Level embeddings**: For positive integer l, the map f(z) ↦ f(lz) sends G_k(N, χ) → G_k(lN, χ).

```lean
/-- Level embedding: f(z) ↦ f(lz) from G_k(N,χ) to G_k(lN,χ). — [Miy] Lemma 4.6.1 -/
noncomputable def levelEmbed (l : ℕ+) :
    ModularFormCharSpace N k χ →ₗ[ℂ] ModularFormCharSpace (l * N) k χ

/-- S_k^1(N, χ): cusp forms generated from lower levels.
    = Σ_{M,l} {f(lz) | f ∈ S_k(M, χ), m_χ | M, M | N, M ≠ N} — [Miy] p.162 -/
def cuspFormsFromLowerLevels (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) :
    Submodule ℂ (CuspFormCharSpace N k χ)

/-- S_k^0(N, χ): the orthocomplement of S_k^1(N, χ) w.r.t. Petersson.
    = (S_k^1(N, χ))⊥ — [Miy] p.162 -/
def cuspFormsPrimitive (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) :
    Submodule ℂ (CuspFormCharSpace N k χ) :=
  (cuspFormsFromLowerLevels N k χ)ᗮ

/-- A primitive form of conductor N: common eigenfunction of all T(n) with (n,N)=1,
    with a₁ = 1, lying in S_k^0(N, χ). — [Miy] p.164 -/
def IsPrimitiveForm (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma0 N) k) : Prop :=
  IsCommonEigenfunction f ∧ fourierCoeff f 1 = 1 ∧ f ∈ cuspFormsPrimitive N k χ
```

### Key Theorems (following Miyake §4.6 in order)

1. **Hecke's Lemma** (`hecke_lemma`): — [Miy] Lemma 4.6.3
   If f ∈ G_k(N, χ) and α = [a b; c d] ∈ Δ₀(N) with det(α) > 1, gcd(det,N) = 1,
   (a,b,c,d) = 1, and f|_k α ∈ G_k(N, χ), then f = 0.

2. **Conductor theorem** (`conductor_theorem`): — [Miy] Thm 4.6.4
   If f(z+1) = f(z), f(lz) ∈ G_k(N, χ), then:
   - If l·m_χ | N: f ∈ G_k(N/l, χ)
   - If l·m_χ ∤ N: f = 0

3. **Coprime sieving** (`coprime_sieve`): — [Miy] Lemma 4.6.5
   If f ∈ G_k(N, χ) and g(z) = Σ_{(n,L)=1} a_n e^{2πinz}, then g ∈ G_k(M, χ) where
   M = N · Π_{p|L, p|N} p · Π_{p|L, p∤N} p²

4. **Level-raising commutative diagrams**: — [Miy] Lemma 4.6.6
   The diagrams relating T(p) at different levels commute.

5. **Square-free decomposition** (`square_free_decomp`): — [Miy] Lemma 4.6.7
   If l > 1 is square-free and a_n = 0 for all n prime to l, then f = Σ_{p|l} g_p(pz)
   with g_p ∈ G_k(Nl, χ).

6. **General decomposition** (`general_decomp`): — [Miy] Thm 4.6.8 (**Main Lemma**)
   If l ≥ 1 and a_n = 0 for all n prime to l:
   - If (l, N/m_χ) = 1: f = 0
   - Otherwise: f = Σ_{p|(l,N/m_χ)} f_p(pz) with f_p ∈ S_k(N/p, χ) for all prime p of (l, N/m_χ)

7. **Stability under Hecke operators**: — [Miy] Lemma 4.6.10
   S_k^1(N, χ) and S_k^0(N, χ) are stable under T(n) for (n,N) = 1.

8. **Non-vanishing of a₁** (`nonvanishing_a1`): — [Miy] Lemma 4.6.11
   If f ∈ S_k^0(N, χ) is a common eigenfunction of T(n) for n prime to some L, and a₁ ≠ 0,
   then f|T(n) = a_n·f for all n prime to L.

9. **Strong Multiplicity One** (`strongMultiplicityOne`): — [Miy] Thm 4.6.12
   (See Phase 9)

10. **Primitive forms are eigenfunctions of full Hecke algebra**: — [Miy] Thm 4.6.13
    Primitive forms are common eigenfunctions of R(N) ∪ R*(N).

11. **Existence of primitive form at divisor level** (`primitive_at_divisor`): — [Miy] Cor 4.6.14
    If f ∈ S_k(N, χ) is a common eigenfunction of T(n) with eigenvalues a_n for n prime to N,
    then ∃ M | N and g ∈ S_k^0(M, χ) primitive with g|T(n) = a_n·g.

12. **ω_N action on primitive forms**: — [Miy] Thm 4.6.15
    Twisting by ω_N gives isomorphisms between primitive form spaces.

13. **Local theory at primes**: — [Miy] Thm 4.6.16
    Detailed structure of primitive form Fourier coefficients at primes q | N.

### Comparison with Diamond-Shurman

| Concept | Diamond-Shurman | Miyake |
|---------|----------------|--------|
| Old subspace | S_k^old = Σ_{p\|N} i_p(S_k(N/p)²) | S_k^1(N,χ) (from lower levels) |
| New subspace | S_k^new = (S_k^old)⊥ | S_k^0(N,χ) = (S_k^1)⊥ |
| Newform | Normalized eigenform in S_k^new | Primitive form in S_k^0 |
| Main Lemma | Thm 5.7.1 (via projection ops) | Thm 4.6.8 (via conductor) |
| SMO | Thm 5.8.2 (within level only) | **Thm 4.6.12 (full, across levels)** |

### Files

- `Eigenforms/LevelEmbed.lean` — f(z) ↦ f(lz) maps and commutative diagrams
- `Eigenforms/HeckeLemma.lean` — Hecke's Lemma 4.6.3
- `Eigenforms/ConductorTheory.lean` — Conductor theorem 4.6.4
- `Eigenforms/PrimitiveDecomp.lean` — S_k^0/S_k^1 decomposition, Lemmas 4.6.5–4.6.8
- `Eigenforms/PrimitiveForm.lean` — Primitive form definition and properties (4.6.9–4.6.16)

---

## Phase 7: L-functions and Euler Products

**Goal**: Define L(s, f) for eigenforms and prove the Euler product characterization.

**Reference**: [DS] §5.9, [Miy] §4.5 (Thm 4.5.16, Lemma 4.5.15)

### Definitions

```lean
/-- The L-function of a modular form: L(s, f) = Σ_{n≥1} a_n(f) n^{-s}. -/
noncomputable def modularLFunction (f : ModularForm (Gamma1 N) k) (s : ℂ) : ℂ :=
  ∑' n : ℕ+, fourierCoeff f n * (n : ℂ)⁻ˢ

/-- Convergence: L(s, f) converges absolutely for Re(s) > k/2 + 1 (cusp forms)
    or Re(s) > k (non-cusp forms). -/
theorem modularLFunction_convergence (f : CuspForm (Gamma1 N) k) (s : ℂ)
    (hs : k / 2 + 1 < s.re) : Summable (fun n : ℕ+ => ‖fourierCoeff f n * (n : ℂ)⁻ˢ‖)
```

### Key Theorems

1. **Euler product characterization** (`euler_product_iff_normalized_eigenform`):
   — [DS] Thm 5.9.2, [Miy] Thm 4.5.16
   f ∈ M_k(N, χ) is a normalized eigenform ⟺ L(s,f) has Euler product:
   ```
   L(s, f) = Π_p (1 - a_p p^{-s} + χ(p) p^{k-1-2s})⁻¹
   ```

2. **Normalized eigenform characterization** (`normalized_eigenform_iff_coeff_relations`):
   — [DS] Prop 5.8.5
   f is a normalized eigenform ⟺ a₁ = 1, a_{p^r} = a_p a_{p^{r-1}} - χ(p)p^{k-1}a_{p^{r-2}},
   a_{mn} = a_m a_n when (m,n) = 1.

3. **Fourier coefficient bound** (`ramanujan_petersson_weak`):
   — [Miy] (4.5.40), [DS] Prop 5.9.1
   |a_n(f)| = O(n^α) for cusp forms (α = k/2) and non-cusp forms (α = k-1).

### Files

- `Eigenforms/LFunction.lean` — L(s,f) definition, convergence
- `Eigenforms/EulerProduct.lean` — Euler product ↔ normalized eigenform

---

## Phase 8: Main Lemma (Miyake's Decomposition Theorem)

**Goal**: Prove Miyake's Theorem 4.6.8 — the decomposition of cusp forms whose
Fourier coefficients vanish for indices coprime to l.

**Reference**: [Miy] Thm 4.6.8

### Statement

```lean
/-- Miyake's Main Lemma (Thm 4.6.8).
    If f ∈ G_k(N, χ) with a_n = 0 for all n prime to l, and m_χ is the conductor of χ:
    (1) If (l, N/m_χ) = 1, then f = 0.
    (2) If (l, N/m_χ) ≠ 1, then f = Σ_{p | (l, N/m_χ)} f_p(pz) for f_p ∈ S_k(N/p, χ). -/
theorem miyake_decomposition_theorem (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (l : ℕ+) (f : CuspFormCharSpace N k χ)
    (hf : ∀ n : ℕ+, n.val.Coprime l → fourierCoeff f n = 0) :
    (l.val.Coprime (N / conductorOf χ) → f = 0) ∧
    (¬ l.val.Coprime (N / conductorOf χ) →
      ∃ (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ Nat.gcd l (N / conductorOf χ))
        (fp : ∀ p ∈ S, CuspFormCharSpace (N / p) k χ),
        f = ∑ p ∈ S, levelEmbed p (fp p ‹_›))
```

### Proof Structure (following Miyake)

The proof proceeds by induction on the number of prime factors of l:

**Base case** (l prime): Use Theorem 4.6.4 (conductor theorem) — if l | N, then
g(z) = f(z/l) ∈ S_k(Nl, χ) and either f(z) = g(lz) or f = 0.

**Inductive step**: Factor l = p · l' where p is prime. Define h(z) = Σ_{(n,l')=1} a_n e^{2πinz}
and use Lemma 4.6.5 (coprime sieving) to show h ∈ G_k(M, χ) for appropriate M.
Then f - f_p(pz) satisfies the hypothesis for l' and apply induction.

**Key sublemmas needed**:
- Lemma 4.6.5 (coprime sieving) — proved via Lemma 4.6.2 (T(p) level compatibility)
- Lemma 4.6.6 (commutative diagrams for level-p maps)
- Lemma 4.6.7 (square-free case)

### Files

- `Eigenforms/CoprimeSieve.lean` — Lemma 4.6.5
- `Eigenforms/MainLemma.lean` — Theorem 4.6.8

---

## Phase 9: Strong Multiplicity One

**Goal**: Prove Miyake's Theorem 4.6.12.

**Reference**: [Miy] Thm 4.6.12

### Statement

```lean
/-- Strong Multiplicity One (Miyake Thm 4.6.12).
    If f ∈ S_k^0(N, χ) and g ∈ S_k^1(N, χ) are common eigenfunctions of T(n) with the
    same eigenvalue for each n prime to some integer L, then g = c·f. -/
theorem strongMultiplicityOne (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : CuspFormCharSpace N k χ) (g : CuspFormCharSpace N k χ)
    (hf0 : f ∈ cuspFormsPrimitive N k χ)
    (hg1 : g ∈ cuspFormsFromLowerLevels N k χ ⊔ cuspFormsPrimitive N k χ)
    (L : ℕ+)
    (hf_eigen : IsCommonEigenfunction_away L f)
    (hg_eigen : IsCommonEigenfunction_away L g)
    (h_same : ∀ n : ℕ+, n.val.Coprime L → eigenvalue f n = eigenvalue g n) :
    ∃ c : ℂ, g = c • f
```

### Proof (following Miyake pp.163–164)

1. Let f = Σ a_n e^{2πinz} with a₁ ≠ 0 (by Lemma 4.6.11 since f ∈ S_k^0).
   We may assume a₁ = 1 (normalize).

2. Decompose g = g^(0) + g^(1) with g^(0) ∈ S_k^0(N, χ), g^(1) ∈ S_k^1(N, χ).

3. Both g^(0) and g^(1) are common eigenfunctions of T(n) with eigenvalue a_n
   for n prime to L (by Lemma 4.6.10: S_k^0 and S_k^1 are stable under T(n)).

4. **Claim: g^(0) = b₁·f.** By Lemma 4.6.11, b₁ ≠ 0 implies g^(0)|T(n) = b_n·g^(0)
   where b_n = a_n for n prime to L. Since g^(0) ∈ S_k^0(N, χ) and f ∈ S_k^0(N, χ)
   are both eigenfunctions with the same eigenvalues, applying Theorem 4.6.8
   to h = g^(0) - b₁·f shows h ∈ S_k^1(N, χ). But h ∈ S_k^0(N, χ) too, so h = 0.

5. **Claim: g^(1) = 0.** If g^(1) ≠ 0, by Lemma 4.6.11 we get c₁' ≠ 0 and then
   h(z) = g^(0) - c₁'·f(z) has a₁ coefficient zero. Applying Theorem 4.6.8 gives
   h ∈ S_k^1(N, χ), contradicting f ∈ S_k^0(N, χ).

6. Therefore g = g^(0) = b₁·f.

### Corollaries

```lean
/-- Corollary 4.6.14: Every eigenform has a primitive form at some divisor level. -/
theorem exists_primitive_at_divisor (f : CuspFormCharSpace N k χ)
    (hf : IsCommonEigenfunction f) :
    ∃ (M : ℕ) (hM : M ∣ N) (g : CuspFormCharSpace M k χ),
      IsPrimitiveForm M k χ g ∧ ∀ n, n.Coprime N → eigenvalue g n = eigenvalue f n

/-- Normalized primitive forms with the same eigenvalues are equal. -/
theorem primitive_determined_by_eigenvalues (f g : CuspFormCharSpace N k χ)
    (hf : IsPrimitiveForm N k χ f) (hg : IsPrimitiveForm N k χ g)
    (h : ∀ n : ℕ+, n.val.Coprime N → eigenvalue f n = eigenvalue g n) :
    f = g
```

### Files

- `Eigenforms/StrongMultiplicityOne.lean` — Theorem 4.6.12 and corollaries

---

## Dependency Graph

```
Phase 1 ─→ Phase 2 ─→ Phase 3 (T_n + Fourier)
  ✅           ✅          ✅
                  ↘                     ↓
Phase 4 (Petersson) ← ── ── ── ── ┘
   ✅           ↓
Phase 5 (Adjoints + eigenforms) ←── Phase 3
   ⚠️ active    ↓
Phase 6 (Primitive forms) ←── Phases 3, 4, 5
   ⚠️ 40%      ↓
Phase 7 (L-functions) ←── Phase 3  ← NOW UNBLOCKED
   ❌           ↓
Phase 8 (Main Lemma) ←── Phase 6
   ❌           ↓
Phase 9 (SMO) ←── Phases 6, 8
   ❌
```

**Parallelism NOW**: Phase 7 (L-functions) can start immediately (Phase 3 is complete).
Phase 6 can continue while Phase 5 finishes.

**Critical path to SMO**: Phase 5 → Phase 6 → Phase 8 → Phase 9.

---

## Estimated Scope

*Updated 2026-04-17 with actual line counts post-refactor*

| Phase | Est. lines | Actual lines | Sorries | Status |
|-------|------------|-------------|---------|--------|
| 1: Gamma1 pair | ~600 | 640 | 0 | ✅ COMPLETE |
| 2: Diamond + T_p | ~800 | 2345 (Gamma1Pair+HeckeT_p+HeckeAction) | 0 | ✅ COMPLETE |
| 3: T_n + Fourier | ~700 | 3532 (HeckeT_n+FourierHecke) | 0 | ✅ COMPLETE |
| 4: Petersson | ~1000 | 1520+ | 0 | ✅ COMPLETE |
| 5: Adjoints + eigenforms | ~700 | 2643 | 2 | ⚠️ ACTIVE (other worker) |
| 6: Primitive forms | ~1500 | 1725+96 | 2 | ⚠️ 40% |
| 7: L-functions | ~500 | 0 | — | ❌ UNBLOCKED |
| 8: Main Lemma | ~1000 | 0 | — | ❌ |
| 9: SMO | ~400 | 0 | — | ❌ |
| **Total** | **~7200** | **~12500** | **4** | **~75%** |

**Additional infrastructure (not in original plan):**

| File | Lines | Sorries | Purpose |
|------|-------|---------|---------|
| GL2/MultiplicationTable.lean | 1183 | 0 | Shimura 3.24 multiplication |
| GL2/HeckeModularForm.lean | 562 | 0 | Hecke ops on modular forms + `heckeRingHom` |
| GL2/Degree.lean | 196 | 0 | Degree map |
| GL2/CongruenceIndex.lean | 271 | 0 | Index formulas |
| GLn/CongruenceHecke.lean | 6117 | 0 | Shimura 3.35 (Γ₀(N) surjection) |
| GLn/SL2Surjection.lean | 244 | 0 | Strong approximation |

**Ring-hom refactor (2026-04-17, ~4500 LOC):** see "Existing Infrastructure" table above.
Provides `heckeRingHom_Gamma0`, `heckeRingHomCharSpaceOne`, `heckeT_coprimeRestrict`,
`CharacterDecomp`, `CharSpaceIso`, plus Shimura Prop 3.34 infrastructure.

---

## Open Design Questions

1. **Predicate vs structure for eigenforms?**
   Use predicates (`IsHeckeEigenform`, `IsPrimitiveForm`) for flexibility — structures
   can be provided as convenience wrappers but predicates compose better with
   existing mathlib types.

2. **Miyake's G_k(N, χ) vs Diamond-Shurman's M_k(Γ₁(N))?**
   Both are needed. G_k(N, χ) is the χ-eigenspace of M_k(Γ₁(N)). Build both and
   prove they're related by the character decomposition.

3. **How to handle integration over Γ\ℍ?**
   The standard domain/reduction lemmas for `SL(2,ℤ)` are already in mathlib, so the question is
   which integration interface to build on top of them. Could use:
   - Explicit fundamental domain + change of variables
   - Abstract quotient measure theory
   Full convergence proof is required — no axiomatization.

4. **Which spectral theorem?**
   Need simultaneous diagonalization of commuting normal operators on
   finite-dimensional ℂ-inner product space. May need to build this if not in Mathlib.

5. **Conductor of Dirichlet character**
   Mathlib has Dirichlet characters but we need the conductor m_χ.
   Check if `DirichletCharacter.conductor` exists or needs to be built.
