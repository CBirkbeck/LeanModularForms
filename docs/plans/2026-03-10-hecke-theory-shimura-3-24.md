# Hecke Ring Theory: Shimura Theorem 3.24 and Hecke Operators

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking. Each ticket is independent once its dependencies are met. Multiple workers can run in parallel on independent tickets.

**Goal:** Develop a complete, mathlib-quality theory of Hecke rings for GL_n(Q)/SL_n(Z), prove Shimura's Theorem 3.24 (the multiplication table for n=2), and define Hecke operators acting on modular forms.

**Architecture:** We build in layers on top of the existing sorry-free abstract Hecke ring. Layer 0 (done) is the abstract ring. Layer 1 enhances it with degree maps and commutativity criteria. Layer 2 instantiates for GL_n. Layer 3 develops the structure theory (coset reps, degree formulas, ring properties). Layer 4 specializes to n=2 and proves Theorem 3.24. Layer 5 defines Hecke operators on modular forms via mathlib's `SlashAction`.

**Tech Stack:** Lean 4, Mathlib (`GeneralLinearGroup`, `SpecialLinearGroup`, `SlashAction`, `ModularForm`, `Commensurable`, `DoubleCoset`, `Finsupp`)

**Reference:** Shimura, "Introduction to the Arithmetic Theory of Automorphic Functions", Chapter 3 (sections 3.1-3.4)

---

## Progress Tracker

| Ticket | Name | Status | Assignee | Dependencies | Files |
|--------|------|--------|----------|--------------|-------|
| **1** | Abstract Ring: Degree Map | Not Started | - | None | `AbstractHeckeRing/Degree.lean` |
| **2** | Abstract Ring: Anti-Involution Commutativity | In Progress | Claude | None | `AbstractHeckeRing/Commutativity.lean` |
| **3** | GL_n ArithmeticGroupPair | Not Started | - | None | `GLn/Basic.lean` |
| **4** | Diagonal Representatives & T(a₁,...,aₙ) | Not Started | - | 3 | `GLn/DiagonalCosets.lean` |
| **5** | Commutativity of R(Γ,Δ) via Transpose | Not Started | - | 2, 3 | `GLn/Commutativity.lean` |
| **6** | Coset Decomposition & Degree Formulas | Not Started | - | 4 | `GLn/CosetDecomposition.lean`, `GLn/Degree.lean` |
| **7** | Coprime Product & Scalar Multiplication | Not Started | - | 4, 6 | `GLn/CoprimeMul.lean` |
| **8** | Prime Decomposition & Polynomial Ring | Not Started | - | 7 | `GLn/PrimeDecomposition.lean`, `GLn/PolynomialRing.lean` |
| **9** | n=2 Specialization: Theorem 3.24 | Not Started | - | 8 | `GL2/Basic.lean`, `GL2/MultiplicationTable.lean` |
| **10** | Hecke Operators on Modular Forms | Not Started | - | 9, 1 | `GL2/HeckeOperator.lean` |

### Parallelism Guide

```
Tickets 1, 2, 3 are FULLY INDEPENDENT -- run all three in parallel

After 3 completes:
  Ticket 4 can start (needs 3)
  Ticket 5 can start (needs 2 + 3)

After 4 completes:
  Ticket 6 can start (needs 4)

After 6 completes:
  Ticket 7 can start (needs 4, 6)

After 7 completes:
  Ticket 8 can start (needs 7)

After 8 completes:
  Ticket 9 can start (needs 8)

After 9 + 1 complete:
  Ticket 10 can start (needs 9, 1)
```

---

## File Structure

All new files go under `LeanModularForms/HeckeRIngs/`. The existing abstract ring files are untouched except for adding new files alongside them.

```
LeanModularForms/HeckeRIngs/
  AbstractHeckeRing.lean              -- existing re-export hub (MODIFY: add new imports)
  AbstractHeckeRing/
    Basic.lean                         -- existing, untouched
    Multiplication.lean                -- existing, untouched
    Module.lean                        -- existing, untouched
    Associativity.lean                 -- existing, untouched
    Ring.lean                          -- existing, untouched
    Degree.lean                        -- NEW (Ticket 1): deg : 𝕋 P ℤ →+* ℤ
    Commutativity.lean                 -- NEW (Ticket 2): anti-involution → CommRing
  GLn/
    Basic.lean                         -- NEW (Ticket 3): ArithmeticGroupPair for GL_n
    DiagonalCosets.lean                -- NEW (Ticket 4): T(a₁,...,aₙ), diagonal reps
    Commutativity.lean                 -- NEW (Ticket 5): transpose instance
    CosetDecomposition.lean            -- NEW (Ticket 6a): upper-triangular left coset reps
    Degree.lean                        -- NEW (Ticket 6b): degree formulas, Gaussian binomials
    CoprimeMul.lean                    -- NEW (Ticket 7): Prop 3.16, 3.17
    PrimeDecomposition.lean            -- NEW (Ticket 8a): R = ⊗ R_p
    PolynomialRing.lean                -- NEW (Ticket 8b): Theorem 3.20
  GL2/
    Basic.lean                         -- NEW (Ticket 9a): n=2 defs, T(a,d), T(m)
    MultiplicationTable.lean           -- NEW (Ticket 9b): Theorem 3.24
    HeckeOperator.lean                 -- NEW (Ticket 10): f |[ΓαΓ]_k
```

---

## Ticket 1: Abstract Ring — Degree Map

**Status:** Not Started
**Dependencies:** None
**Assignee:** -
**Reference:** Shimura Proposition 3.3

### Goal

Define `deg : 𝕋 P ℤ →+* ℤ`, the degree ring homomorphism that sends a double coset `HgH` to the number of left cosets it contains: `deg(HgH) = [H : H ∩ gHg⁻¹]`.

### Files

- Create: `LeanModularForms/HeckeRIngs/AbstractHeckeRing/Degree.lean`
- Modify: `LeanModularForms/HeckeRIngs/AbstractHeckeRing.lean` (add import)

### Key Definitions

```lean
-- The degree of a single double coset
noncomputable def T'_deg (P : ArithmeticGroupPair G) (D : T' P) : ℤ :=
  Fintype.card (decompQuot P D)

-- The degree ring homomorphism
noncomputable def deg (P : ArithmeticGroupPair G) : 𝕋 P ℤ →+* ℤ where
  toFun f := f.sum fun D a => a * T'_deg P D
  map_one' := ...
  map_mul' := ...
  map_zero' := ...
  map_add' := ...
```

### API to provide

```lean
-- Notation
scoped notation "deg" => HeckeRing.deg

-- Core evaluation lemma
@[simp] lemma deg_T_single (D : T' P) (a : ℤ) :
    deg P (T_single P ℤ D a) = a * T'_deg P D

-- Degree is positive on basis elements
lemma T'_deg_pos (D : T' P) : 0 < T'_deg P D

-- Degree of identity
@[simp] lemma T'_deg_T_one : T'_deg P (T_one P) = 1

@[simp] lemma deg_one : deg P 1 = 1

-- Multiplicativity (this IS the hard part — needs m' sum formula)
-- deg(D1) * deg(D2) = ∑_D m'(D1,D2,D) * deg(D)
-- which implies deg is a ring hom
lemma deg_mul (f g : 𝕋 P ℤ) : deg P (f * g) = deg P f * deg P g
```

### Tasks

- [ ] **Step 1:** Create `Degree.lean` with imports from `Ring.lean`. Define `T'_deg` and state `T'_deg_pos`, `T'_deg_T_one`.
- [ ] **Step 2:** Prove `T'_deg_T_one` (the identity double coset H1H has one left coset, using `subsingleton_decompQuot_T_one`).
- [ ] **Step 3:** Prove `T'_deg_pos` (decompQuot is a nonempty Fintype).
- [ ] **Step 4:** Define `deg` as a `RingHom`. The additive part is straightforward (Finsupp.sum is additive). The multiplicative part requires the key identity: `∑_D m'(D₁,D₂,D) * |Q(D)| = |Q(D₁)| * |Q(D₂)|` (Shimura's degree formula for products). State this as a lemma and prove it.
- [ ] **Step 5:** Prove the API lemmas (`deg_T_single`, `deg_one`, etc.).
- [ ] **Step 6:** Add import to `AbstractHeckeRing.lean`. Run `lake build`. Verify sorry-free.
- [ ] **Step 7:** Commit.

### Key Mathematical Insight

The multiplicativity `deg(f * g) = deg(f) * deg(g)` comes from the fact that `∑_D m'(D₁,D₂,D) * |Q(D)| = |Q(D₁)| * |Q(D₂)|`. This is because every pair `(i,j) ∈ Q(D₁) × Q(D₂)` maps to exactly one `D` in the product (via `mulMap`), and each `D` with its `m'` pairs accounts for exactly `m' * |Q(D)|` of the total `|Q(D₁)| * |Q(D₂)|` pairs.

---

## Ticket 2: Abstract Ring — Anti-Involution Commutativity

**Status:** Not Started
**Dependencies:** None
**Assignee:** -
**Reference:** Shimura Proposition 3.8

### Goal

If `(G, H, Δ)` admits an anti-automorphism `ι : G →* Gᵐᵒᵖ` that preserves H and Δ, then `R(H,Δ)` is commutative. Provide a `CommRing` instance conditionally.

### Files

- Create: `LeanModularForms/HeckeRIngs/AbstractHeckeRing/Commutativity.lean`
- Modify: `LeanModularForms/HeckeRIngs/AbstractHeckeRing.lean` (add import)

### Key Definitions

```lean
/-- An anti-involution of an ArithmeticGroupPair is an anti-automorphism ι : G →* Gᵐᵒᵖ
    that preserves both H and Δ. The prototypical example is matrix transpose. -/
structure AntiInvolution (P : ArithmeticGroupPair G) where
  toFun : G →* MulOpposite G
  involutive : ∀ g, (toFun (toFun g).unop).unop = g
  map_H : ∀ h ∈ P.H, (toFun h).unop ∈ P.H
  map_Δ : ∀ d ∈ P.Δ, (toFun d).unop ∈ P.Δ

/-- An anti-involution induces an involution on double cosets: HgH ↦ Hι(g)H.
    Since ι is anti, ι(HgH) = ι(H)ι(g)ι(H) = Hι(g)H. -/
noncomputable def AntiInvolution.onT' (ι : AntiInvolution P) : T' P → T' P

/-- The induced ring involution on the Hecke ring. -/
noncomputable def AntiInvolution.ringInvolution (ι : AntiInvolution P) :
    𝕋 P ℤ →+* (𝕋 P ℤ)ᵐᵒᵖ

/-- Key: ι(D₁ * D₂) = ι(D₂) * ι(D₁) because ι is anti.
    But ι(D) = D for diagonal representatives, so D₁ * D₂ = D₂ * D₁. -/
-- Actually the general statement is: if ι fixes every double coset, then commutative.
-- Shimura's Prop 3.8 says: '(ΓαΓ) = ΓαΓ for all α implies commutativity.

/-- If the anti-involution fixes every double coset, the Hecke ring is commutative. -/
theorem commRing_of_antiInvolution (ι : AntiInvolution P)
    (h_fix : ∀ D : T' P, ι.onT' D = D) :
    Commutative (· * · : 𝕋 P ℤ → 𝕋 P ℤ → 𝕋 P ℤ)

noncomputable def instCommRing_of_antiInvolution (ι : AntiInvolution P)
    (h_fix : ∀ D : T' P, ι.onT' D = D) :
    CommRing (𝕋 P ℤ)
```

### API to provide

```lean
-- The anti-involution reverses multiplication
lemma AntiInvolution.map_mul_rev (ι : AntiInvolution P) (f g : 𝕋 P ℤ) :
    ι.ringMap (f * g) = ι.ringMap g * ι.ringMap f

-- Fixed-point criterion
lemma AntiInvolution.onT'_eq_of_same_set (ι : AntiInvolution P) (D : T' P)
    (h : ι.onT' D).set = D.set) : ι.onT' D = D
```

### Tasks

- [x] **Step 1:** Create `Commutativity.lean`. Define `AntiInvolution` structure.
- [x] **Step 2:** Define `AntiInvolution.onT'` — sends `T_mk g` to `T_mk (ι g).unop`. Prove it's well-defined (`bar_doubleCoset_eq`), involutive (`onT'_involutive`).
- [ ] **Step 3:** ~~Define `AntiInvolution.ringMap`~~ (skipped: direct proof via `m_comm` is cleaner). Prove `m'_comm_of_onT'_eq` — **1 sorry remaining** (bijection between counting sets).
- [x] **Step 4:** Prove `mul_comm_of_antiInvolution` via `𝕋.induction_linear` + `m_comm_of_onT'_eq` + `smul_comm`.
- [x] **Step 5:** Package as `instCommRing_of_antiInvolution`.
- [x] **Step 6:** Add import. `lake build` passes (1 sorry in `m'_comm_of_onT'_eq`).
- [ ] **Step 7:** Fill `m'_comm_of_onT'_eq` sorry, then commit.

---

## Ticket 3: GL_n ArithmeticGroupPair

**Status:** Not Started
**Dependencies:** None
**Assignee:** -
**Reference:** Shimura §3.2 (page 55-56), Lemma 3.10

### Goal

Construct the canonical `ArithmeticGroupPair (GL (Fin n) ℚ)` with `H = SL_n(ℤ)` (embedded in GL_n(ℚ)) and `Δ = {α ∈ M_n(ℤ) | det(α) > 0}` (embedded in GL_n(ℚ)). Prove the commensurator condition.

### Files

- Create: `LeanModularForms/HeckeRIngs/GLn/Basic.lean`

### Key Definitions

```lean
/-- Embed SL_n(ℤ) into GL_n(ℚ) via the inclusion ℤ ↪ ℚ. -/
noncomputable def SLnZ_to_GLnQ (n : ℕ) :
    SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ

/-- SL_n(ℤ) as a subgroup of GL_n(ℚ). -/
noncomputable def SLnZ_subgroup (n : ℕ) : Subgroup (GL (Fin n) ℚ) :=
  (SLnZ_to_GLnQ n).range

/-- Positive-determinant integer matrices as a submonoid of GL_n(ℚ).
    An element is in Δ iff it can be represented by an integer matrix with
    positive determinant. -/
noncomputable def posDetInt_submonoid (n : ℕ) : Submonoid (GL (Fin n) ℚ)

/-- The standard arithmetic group pair for number theory. -/
noncomputable def GL_pair (n : ℕ) [NeZero n] : ArithmeticGroupPair (GL (Fin n) ℚ) where
  H := SLnZ_subgroup n
  Δ := posDetInt_submonoid n
  h₀ := ... -- SL_n(Z) ⊆ Δ (det = 1 > 0, entries in ℤ)
  h₁ := ... -- Δ ⊆ commensurator(SL_n(Z))

-- Notation
scoped notation "Γₙ" => SLnZ_subgroup
scoped notation "Δₙ" => posDetInt_submonoid
```

### API to provide

```lean
-- Abbreviation for the Hecke ring
abbrev HeckeAlgebra (n : ℕ) [NeZero n] := 𝕋 (GL_pair n) ℤ

-- Coercion: integer matrix with pos det → element of Δ
def intMat_to_delta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    (GL_pair n).Δ

-- Coercion: integer matrix with pos det → double coset
def intMat_to_T' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    T' (GL_pair n) := T_mk _ (intMat_to_delta A hdet)

-- Basic properties
lemma SLnZ_subgroup_le_posDetInt : (SLnZ_subgroup n).toSubmonoid ≤ posDetInt_submonoid n

-- The commensurator condition: key lemma
lemma posDetInt_le_commensurator :
    posDetInt_submonoid n ≤ (commensurator (SLnZ_subgroup n)).toSubmonoid
```

### Tasks

- [ ] **Step 1:** Create `GLn/Basic.lean`. Set up imports (`GeneralLinearGroup`, `SpecialLinearGroup`, `Commensurable`, the abstract Hecke ring).
- [ ] **Step 2:** Define `SLnZ_to_GLnQ` — the group homomorphism mapping SL_n(ℤ) → GL_n(ℚ) via the ring map `ℤ → ℚ`. Use `SpecialLinearGroup.map (Int.castRingHom)` composed with the inclusion SL → GL.
- [ ] **Step 3:** Define `SLnZ_subgroup` as the range of this homomorphism. Prove basic properties (it's a subgroup, contains 1, closed under multiplication and inverse).
- [ ] **Step 4:** Define `posDetInt_submonoid` — the submonoid of GL_n(ℚ) consisting of matrices that are (equivalent to) integer matrices with positive determinant. This needs careful formulation: an element g ∈ GL_n(ℚ) is in Δ iff all entries of g.val are in the image of ℤ → ℚ and det(g.val) > 0 (as a rational, i.e., the numerator is positive).
- [ ] **Step 5:** Prove `SLnZ_subgroup_le_posDetInt` — SL_n(ℤ) elements have det = 1 > 0 and integer entries.
- [ ] **Step 6:** Prove `posDetInt_le_commensurator` — this is the hardest part. For α ∈ Δ, we need `[SL_n(ℤ) : SL_n(ℤ) ∩ αSL_n(ℤ)α⁻¹] < ∞`. The key idea: if α has integer entries with det d > 0, then αℤⁿ ⊇ dℤⁿ, so the conjugate `αSL_n(ℤ)α⁻¹` contains the congruence subgroup Γ(d²), which has finite index.
- [ ] **Step 7:** Assemble `GL_pair`. Define convenience API.
- [ ] **Step 8:** Run `lake build`. Verify sorry-free.
- [ ] **Step 9:** Commit.

### Important Notes for Workers

- The embedding `ℤ → ℚ` in mathlib is `Int.cast` or `algebraMap ℤ ℚ`. Use `Matrix.map A (algebraMap ℤ ℚ)` to cast integer matrices.
- `GL n ℚ` is `(Matrix (Fin n) (Fin n) ℚ)ˣ`. To create an element, use `GeneralLinearGroup.mkOfDetNeZero`.
- The commensurator proof (Step 6) is the most substantial. It may help to first prove that Γ(d) = {γ ∈ SL_n(ℤ) | γ ≡ 1 mod d} has finite index in SL_n(ℤ), and that αΓ(d²)α⁻¹ ⊆ SL_n(ℤ) when α ∈ M_n(ℤ) with det α = d.

---

## Ticket 4: Diagonal Representatives & T(a₁,...,aₙ)

**Status:** Not Started
**Dependencies:** Ticket 3
**Assignee:** -
**Reference:** Shimura §3.2 (page 56-57), Lemma 3.13

### Goal

Define the double coset elements `T(a₁,...,aₙ)` corresponding to diagonal matrices `diag[a₁,...,aₙ]` in the Hecke ring. Prove that every double coset has a diagonal representative (Smith normal form), establishing that the `T(a₁,...,aₙ)` span R(Γ,Δ).

### Files

- Create: `LeanModularForms/HeckeRIngs/GLn/DiagonalCosets.lean`

### Key Definitions

```lean
/-- The diagonal matrix diag[a₁,...,aₙ] as an element of GL_n(ℚ),
    given positive integers aᵢ with a_{i+1} ∣ aᵢ. -/
noncomputable def diagMat {n : ℕ} (a : Fin n → ℕ+) : GL (Fin n) ℚ

/-- T(a₁,...,aₙ) = Γ·diag[a₁,...,aₙ]·Γ as a double coset. -/
noncomputable def T_diag {n : ℕ} [NeZero n] (a : Fin n → ℕ+)
    (hdiv : ∀ i : Fin (n-1), (a i.castSucc : ℕ) ∣ (a i.succ : ℕ)) :
    T' (GL_pair n)

/-- T(a₁,...,aₙ) as an element of the Hecke ring (with coefficient 1). -/
noncomputable def T_elem {n : ℕ} [NeZero n] (a : Fin n → ℕ+)
    (hdiv : ∀ i : Fin (n-1), (a i.castSucc : ℕ) ∣ (a i.succ : ℕ)) :
    HeckeAlgebra n := T_single _ ℤ (T_diag a hdiv) 1

-- Notation: for readability
scoped notation "T(" a ")" => T_elem a (by decide)  -- when divisibility is decidable
```

### Key Theorems

```lean
/-- Smith normal form for integer matrices: every α ∈ Δ is equivalent
    (under left and right SL_n(ℤ) multiplication) to a diagonal matrix
    diag[a₁,...,aₙ] with a_{i+1} ∣ aᵢ and all aᵢ > 0.
    This is the elementary divisor theorem. -/
theorem exists_diagonal_representative {n : ℕ} [NeZero n]
    (α : (GL_pair n).Δ) :
    ∃ (a : Fin n → ℕ+) (hdiv : ∀ i : Fin (n-1), (a i.castSucc : ℕ) ∣ (a i.succ : ℕ)),
      T_mk (GL_pair n) α = T_diag a hdiv

/-- The diagonal representative is unique (elementary divisors are unique). -/
theorem diagonal_representative_unique {n : ℕ} [NeZero n]
    (a b : Fin n → ℕ+)
    (ha : ∀ i : Fin (n-1), (a i.castSucc : ℕ) ∣ (a i.succ : ℕ))
    (hb : ∀ i : Fin (n-1), (b i.castSucc : ℕ) ∣ (b i.succ : ℕ))
    (heq : T_diag a ha = T_diag b hb) : a = b

/-- The Hecke ring is spanned by T(a₁,...,aₙ) elements over ℤ. -/
theorem T_diag_span {n : ℕ} [NeZero n] (f : HeckeAlgebra n) :
    ∃ (S : Finset (Σ (a : Fin n → ℕ+), ∀ i : Fin (n-1), (a i.castSucc : ℕ) ∣ (a i.succ : ℕ)))
      (c : S → ℤ),
      f = ∑ s ∈ S, c s • T_elem s.1 s.2

/-- The anti-automorphism ᵗ fixes T(a₁,...,aₙ) since ᵗ(diag[a]) = diag[a]. -/
theorem T_diag_transpose_eq {n : ℕ} [NeZero n]
    (a : Fin n → ℕ+)
    (hdiv : ∀ i : Fin (n-1), (a i.castSucc : ℕ) ∣ (a i.succ : ℕ)) :
    -- the transpose anti-involution fixes T_diag a
    sorry -- statement depends on Ticket 5's anti-involution definition
```

### Tasks

- [ ] **Step 1:** Create `GLn/DiagonalCosets.lean`. Import from `GLn/Basic.lean`.
- [ ] **Step 2:** Define `diagMat` using `Matrix.diagonal` and `GeneralLinearGroup.mkOfDetNeZero` (det of diagonal = product of entries, which is positive for ℕ+ entries).
- [ ] **Step 3:** Define `T_diag` and `T_elem`. Prove basic properties: `T_diag` with all 1s equals `T_one`.
- [ ] **Step 4:** Prove `exists_diagonal_representative` — this is the Smith normal form theorem for ℤ-matrices, proved via elementary row/column operations (which correspond to left/right multiplication by elementary matrices in SL_n(ℤ)). This is substantial. Strategy: prove by induction on n, using the Euclidean algorithm to clear the first row and column.
- [ ] **Step 5:** Prove `diagonal_representative_unique` — the elementary divisors are unique because they are the GCD structure of the minors.
- [ ] **Step 6:** Prove `T_diag_span` — follows from `exists_diagonal_representative`.
- [ ] **Step 7:** Run `lake build`. Verify.
- [ ] **Step 8:** Commit.

### Notes

- The Smith normal form proof (Step 4) is the most technically demanding part of this entire plan. If it's too large, it should be broken into a sub-ticket.
- Check if mathlib has `Matrix.SmithNormalForm` or similar. If not, this could be a significant standalone contribution.
- An alternative approach: prove a weaker version first (existence of diagonal representative for GL_n(ℚ)/SL_n(ℤ) specifically, using the Hermite normal form as an intermediate step), and add uniqueness later.

---

## Ticket 5: Commutativity of R(Γ,Δ) via Transpose

**Status:** Not Started
**Dependencies:** Tickets 2, 3
**Assignee:** -
**Reference:** Shimura Proposition 3.8 applied to GL_n

### Goal

Prove that the Hecke ring `HeckeAlgebra n` is commutative by exhibiting the transpose as an anti-involution that fixes every double coset.

### Files

- Create: `LeanModularForms/HeckeRIngs/GLn/Commutativity.lean`

### Key Definitions

```lean
/-- Matrix transpose as an anti-automorphism G → Gᵐᵒᵖ for GL_n. -/
noncomputable def transpose_anti : GL (Fin n) ℚ →* (GL (Fin n) ℚ)ᵐᵒᵖ

/-- Transpose preserves SL_n(ℤ): if det(A) = 1 then det(Aᵀ) = 1. -/
lemma transpose_mem_SLnZ (g : GL (Fin n) ℚ) (hg : g ∈ SLnZ_subgroup n) :
    (transpose_anti g).unop ∈ SLnZ_subgroup n

/-- Transpose preserves Δ: if A has integer entries with det > 0,
    so does Aᵀ. -/
lemma transpose_mem_posDetInt (g : GL (Fin n) ℚ) (hg : g ∈ posDetInt_submonoid n) :
    (transpose_anti g).unop ∈ posDetInt_submonoid n

/-- The transpose anti-involution for the GL_n pair. -/
noncomputable def GL_antiInvolution (n : ℕ) [NeZero n] :
    AntiInvolution (GL_pair n)

/-- Transpose fixes diagonal matrices, hence fixes all T(a₁,...,aₙ). -/
lemma transpose_fixes_T_diag :
    (GL_antiInvolution n).onT' (T_diag a hdiv) = T_diag a hdiv

/-- Since every double coset has a diagonal representative, transpose fixes all. -/
noncomputable instance : CommRing (HeckeAlgebra n)
```

### Tasks

- [ ] **Step 1:** Create `GLn/Commutativity.lean`. Import Tickets 2 and 3.
- [ ] **Step 2:** Define `transpose_anti` using `Matrix.transpose` and the fact that `det(Aᵀ) = det(A)`.
- [ ] **Step 3:** Prove `transpose_mem_SLnZ` and `transpose_mem_posDetInt`.
- [ ] **Step 4:** Construct `GL_antiInvolution`.
- [ ] **Step 5:** Prove `transpose_fixes_T_diag` — `diag[a₁,...,aₙ]ᵀ = diag[a₁,...,aₙ]`.
- [ ] **Step 6:** Apply Ticket 2's `commRing_of_antiInvolution` to get `CommRing (HeckeAlgebra n)`. (This needs Ticket 4's `exists_diagonal_representative` to know every double coset is fixed.)
- [ ] **Step 7:** Run `lake build`. Verify.
- [ ] **Step 8:** Commit.

### Important Note

Step 6 actually depends on Ticket 4 (to know every coset has a diagonal rep, hence is fixed by transpose). If Ticket 4 is not done yet, this step can be left as sorry with a clear TODO, and the `CommRing` instance added once Ticket 4 completes.

---

## Ticket 6: Coset Decomposition & Degree Formulas

**Status:** Not Started
**Dependencies:** Ticket 4
**Assignee:** -
**Reference:** Shimura Proposition 3.14, 3.18

### Goal

Prove the explicit left coset decomposition of `T(a₁,...,aₙ)` using upper-triangular matrices, and derive the degree formula using Gaussian binomial coefficients.

### Files

- Create: `LeanModularForms/HeckeRIngs/GLn/CosetDecomposition.lean`
- Create: `LeanModularForms/HeckeRIngs/GLn/Degree.lean`

### Key Definitions (CosetDecomposition.lean)

```lean
/-- Upper-triangular representative for a left coset in T(a₁,...,aₙ).
    These have the form [[a₁, b₁₂, ...], [0, a₂, b₂₃, ...], ..., [0,...,0,aₙ]]
    with 0 ≤ bᵢⱼ < aⱼ. -/
structure UpperTriRep (n : ℕ) (a : Fin n → ℕ+) where
  entries : ∀ (i j : Fin n), i < j → Fin (a j : ℕ)
  -- The matrix: A_{ii} = aᵢ, A_{ij} = entries i j _ for i < j, A_{ij} = 0 for i > j

/-- The set of upper-triangular representatives for T(a₁,...,aₙ). -/
def upperTriReps (n : ℕ) (a : Fin n → ℕ+) : Finset (Matrix (Fin n) (Fin n) ℤ)

/-- Each upper-triangular rep gives a distinct left coset. -/
theorem upperTriReps_disjoint ...

/-- The union of left cosets from upper-triangular reps equals T(a₁,...,aₙ). -/
theorem upperTriReps_cover ...

/-- The left coset decomposition of T(a₁,...,aₙ). -/
theorem T_diag_coset_decomposition (a : Fin n → ℕ+) (hdiv : ...) :
    Fintype.card (decompQuot (GL_pair n) (T_diag a hdiv)) =
    Finset.card (upperTriReps n a)
```

### Key Definitions (Degree.lean)

```lean
/-- Gaussian binomial coefficient: the number of k-dimensional subspaces
    of (ℤ/pℤ)ⁿ. -/
def gaussianBinom (p : ℕ) (n k : ℕ) : ℕ :=
  ∏ i in Finset.range k, (p ^ (n - i) - 1) / (p ^ (k - i) - 1)
  -- Or the cleaner product formula from Shimura

/-- Degree of T(a₁,...,aₙ) equals the number of upper-triangular reps. -/
theorem T'_deg_T_diag (a : Fin n → ℕ+) (hdiv : ...) :
    T'_deg (GL_pair n) (T_diag a hdiv) =
    ∏ i in Finset.range n, ∏ j in Finset.range i, (a j : ℤ)
    -- The exact formula depends on the upper-triangular counting

/-- Shimura Proposition 3.18: when a = (1,...,1,p,...,p) with k p's,
    the degree is the Gaussian binomial c_k^(n). -/
theorem deg_T_diag_prime_power (p : ℕ) [hp : Fact p.Prime] (n k : ℕ) (hk : k ≤ n) :
    T'_deg (GL_pair n) (T_diag (fun i => if i < n - k then 1 else ⟨p, hp.1.pos⟩) ...) =
    gaussianBinom p n k

/-- For n=2: deg(T(pⁱ, pⁱ⁺ᵏ)) = pᵏ⁻¹(p+1) for k > 0.
    This is Theorem 3.24 part (6). -/
theorem deg_T_diag_two (p : ℕ) [hp : Fact p.Prime] (i k : ℕ) (hk : 0 < k) :
    T'_deg (GL_pair 2) (T_diag ![⟨p^i, ...⟩, ⟨p^(i+k), ...⟩] ...) =
    p ^ (k - 1) * (p + 1)
```

### Tasks

- [ ] **Step 1:** Create `GLn/CosetDecomposition.lean`. Define `UpperTriRep` and `upperTriReps`.
- [ ] **Step 2:** Prove that each upper-triangular matrix with the right diagonal and 0 ≤ bᵢⱼ < aⱼ gives a distinct left coset of SL_n(ℤ).
- [ ] **Step 3:** Prove that every left coset in T(a₁,...,aₙ) has such a representative (by reducing modulo aⱼ using SL_n(ℤ) row operations).
- [ ] **Step 4:** Create `GLn/Degree.lean`. Define `gaussianBinom`.
- [ ] **Step 5:** Prove `T'_deg_T_diag` — the degree equals the number of upper-triangular reps.
- [ ] **Step 6:** Prove `deg_T_diag_prime_power` — specialize to the prime power case to get Gaussian binomials.
- [ ] **Step 7:** Run `lake build`. Verify.
- [ ] **Step 8:** Commit.

---

## Ticket 7: Coprime Product & Scalar Multiplication

**Status:** Not Started
**Dependencies:** Tickets 4, 6
**Assignee:** -
**Reference:** Shimura Propositions 3.16, 3.17

### Goal

Prove two key structural results about multiplication in the Hecke ring:
1. When det(α) and det(β) are coprime, `ΓαΓ · ΓβΓ = ΓαβΓ` (the product is a single double coset).
2. Scalar multiplication: `T(c,...,c) · T(b₁,...,bₙ) = T(cb₁,...,cbₙ)`.

### Files

- Create: `LeanModularForms/HeckeRIngs/GLn/CoprimeMul.lean`

### Key Theorems

```lean
/-- Shimura Proposition 3.16: if det(α) is coprime to det(β), then the
    double coset product consists of a single coset with multiplicity 1.
    T(a₁,...,aₙ) · T(b₁,...,bₙ) = T(a₁b₁,...,aₙbₙ) when (∏aᵢ, ∏bᵢ) = 1. -/
theorem T_diag_mul_coprime
    (a b : Fin n → ℕ+)
    (ha : ...) (hb : ...)
    (hcop : Nat.Coprime (∏ i, (a i : ℕ)) (∏ i, (b i : ℕ))) :
    T_elem a ha * T_elem b hb = T_elem (fun i => ⟨a i * b i, ...⟩) ...

/-- Shimura Proposition 3.17: scalar double cosets act by scaling.
    T(c,...,c) · T(b₁,...,bₙ) = T(cb₁,...,cbₙ). -/
theorem T_diag_scalar_mul (c : ℕ+)
    (b : Fin n → ℕ+) (hb : ...) :
    T_elem (fun _ => c) ... * T_elem b hb = T_elem (fun i => ⟨c * b i, ...⟩) ...

/-- Consequence: T(c,...,c) is in the center of the Hecke ring.
    (Also follows from commutativity, but this gives a more explicit proof.) -/
theorem T_scalar_central (c : ℕ+) (f : HeckeAlgebra n) :
    T_elem (fun _ => c) ... * f = f * T_elem (fun _ => c) ...

/-- Multiplicativity for coprime integers (Shimura 3.2.1):
    T(mm') = T(m)T(m') when (m,m') = 1. -/
-- This follows from the coprime product theorem applied to diagonal reps.
```

### Tasks

- [ ] **Step 1:** Create `GLn/CoprimeMul.lean`. Import Tickets 4 and 6.
- [ ] **Step 2:** Prove a matrix-level Chinese Remainder Theorem: if det(α) and det(β) are coprime, then the natural map SL_n(ℤ) → SL_n(ℤ/det(α)ℤ) × SL_n(ℤ/det(β)ℤ) is surjective. This is the key ingredient for Prop 3.16.
- [ ] **Step 3:** Prove `T_diag_mul_coprime` — when dets are coprime, the product ΓαΓ·ΓβΓ consists of exactly one double coset ΓαβΓ with multiplicity 1.
- [ ] **Step 4:** Prove `T_diag_scalar_mul` — scalar matrices commute with everything, so T(c,...,c)·T(b) = T(cb,...,cbₙ). This is simpler: cI commutes with all matrices, so Γ(cI)Γ = Γ(cI) (since cI ∈ center), and the product is immediate.
- [ ] **Step 5:** Run `lake build`. Verify.
- [ ] **Step 6:** Commit.

---

## Ticket 8: Prime Decomposition & Polynomial Ring

**Status:** Not Started
**Dependencies:** Ticket 7
**Assignee:** -
**Reference:** Shimura §3.2 (page 58-60), Theorem 3.20

### Goal

Show that R(Γ,Δ) decomposes as a tensor product over primes, and that each local factor R_p^(n) is a polynomial ring in n generators.

### Files

- Create: `LeanModularForms/HeckeRIngs/GLn/PrimeDecomposition.lean`
- Create: `LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean`

### Key Definitions (PrimeDecomposition.lean)

```lean
/-- The p-local Hecke ring: the subring of R(Γ,Δ) generated by elements
    T(p^{e₁},...,p^{eₙ}) for a fixed prime p. -/
noncomputable def R_p (n : ℕ) [NeZero n] (p : ℕ) [hp : Fact p.Prime] :
    Subring (HeckeAlgebra n)

/-- Every T(a₁,...,aₙ) is a product of T(p^{e₁},...,p^{eₙ}) over primes p,
    and this factorization is unique. -/
theorem T_diag_prime_factorization ...

/-- The Hecke ring decomposes as a restricted tensor product over primes. -/
-- This is a structural statement; the formal tensor product may be hard to state.
-- Instead, we can state the key consequence:
theorem HeckeAlgebra_generated_by_prime_powers {n : ℕ} [NeZero n] :
    Subring.closure
      {f : HeckeAlgebra n | ∃ (p : ℕ) (_ : p.Prime) (a : Fin n → ℕ) (hdiv : ...),
        f = T_elem (fun i => ⟨p ^ a i, ...⟩) ...} = ⊤
```

### Key Definitions (PolynomialRing.lean)

```lean
/-- The k-th generator of R_p^(n): T_k^(n) = T(1,...,1,p,...,p) with n-k ones
    and k p's. -/
noncomputable def T_gen (n : ℕ) [NeZero n] (p : ℕ) [hp : Fact p.Prime] (k : Fin n) :
    HeckeAlgebra n :=
  T_elem (fun i => if i < n - k then 1 else ⟨p, hp.1.pos⟩) ...

/-- Shimura's surjective homomorphism ψ : R_p^(n+1) → R_p^(n) (Lemma 3.19). -/
noncomputable def psi_hom (n : ℕ) [NeZero n] (p : ℕ) [hp : Fact p.Prime] :
    R_p (n+1) p →+* R_p n p

/-- Theorem 3.20: R_p^(n) is a polynomial ring in n variables.
    The generators are T_1^(n), ..., T_n^(n). -/
theorem R_p_isPolynomial (n : ℕ) [NeZero n] (p : ℕ) [hp : Fact p.Prime] :
    ∃ (φ : MvPolynomial (Fin n) ℤ →+* ↥(R_p n p)),
      Function.Surjective φ ∧ RingHom.ker φ = ⊥
    -- Or equivalently: algebraic independence + generation

/-- T_n^(n) = T(p,...,p) is not a zero divisor (Prop 3.17 consequence). -/
theorem T_gen_not_zero_divisor ...
```

### Tasks

- [ ] **Step 1:** Create `GLn/PrimeDecomposition.lean`. Define `R_p` as a subring.
- [ ] **Step 2:** Prove `T_diag_prime_factorization` using unique prime factorization of each aᵢ and the coprime product theorem from Ticket 7.
- [ ] **Step 3:** Create `GLn/PolynomialRing.lean`. Define `T_gen` and `psi_hom`.
- [ ] **Step 4:** Prove Lemma 3.19: ψ is surjective with Ker(ψ) = T(p,...,p) · R_p^(n+1). This uses the multiplicativity established in Ticket 7.
- [ ] **Step 5:** Prove Theorem 3.20 by induction on n. Base case n=1 is clear (R_p^(1) = ℤ[T(p)] ≅ ℤ[X]). Inductive step uses Lemma 3.19.
- [ ] **Step 6:** Run `lake build`. Verify.
- [ ] **Step 7:** Commit.

### Notes

- The polynomial ring isomorphism is conceptually clear but technically involved to formalize. Consider stating it as algebraic independence + generation rather than constructing an explicit `MvPolynomial` isomorphism.
- The key algebraic independence argument (page 60 of Shimura) uses a weight function w and induction. This needs careful formalization.

---

## Ticket 9: n=2 Specialization — Theorem 3.24

**Status:** Not Started
**Dependencies:** Ticket 8
**Assignee:** -
**Reference:** Shimura Theorem 3.24 (page 63)

### Goal

Specialize everything to n=2 and prove the 7 multiplication identities.

### Files

- Create: `LeanModularForms/HeckeRIngs/GL2/Basic.lean`
- Create: `LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean`

### Key Definitions (Basic.lean)

```lean
/-- The GL₂ Hecke ring. -/
abbrev HeckeAlgebra₂ := HeckeAlgebra 2

/-- T(a,d) for n=2: the double coset Γ·diag[a,d]·Γ with a ∣ d. -/
noncomputable def T_ad (a d : ℕ+) (h : (a : ℕ) ∣ (d : ℕ)) : HeckeAlgebra₂ :=
  T_elem ![a, d] (by intro i; fin_cases i; exact h)

/-- T(m) = ∑_{ad=m, a∣d} T(a,d): sum over all divisor pairs. -/
noncomputable def T_m (m : ℕ+) : HeckeAlgebra₂ :=
  ∑ p in (divisorPairs m), T_ad p.1 p.2 p.3

/-- T(p) = T(1,p) for a prime p. -/
noncomputable def T_p (p : ℕ) [hp : Fact p.Prime] : HeckeAlgebra₂ :=
  T_ad 1 ⟨p, hp.1.pos⟩ (one_dvd _)

/-- T(p,p) = T_ad(p,p) — the scalar double coset. -/
noncomputable def T_pp (p : ℕ) [hp : Fact p.Prime] : HeckeAlgebra₂ :=
  T_ad ⟨p, hp.1.pos⟩ ⟨p, hp.1.pos⟩ dvd_refl _

-- Convenient notation
scoped notation "T(" a ", " d ")" => T_ad a d
scoped notation "T(" m ")" => T_m m
```

### Key Theorems (MultiplicationTable.lean)

```lean
/-- Theorem 3.24(1): T(m) = ∑_{ad=m, a∣d} T(a,d). DEFINITIONAL. -/
theorem thm324_1 (m : ℕ+) :
    T_m m = ∑ p in divisorPairs m, T_ad p.1 p.2 p.3 := rfl

/-- Theorem 3.24(2): T(1, pᵏ) = T(pᵏ) - T(p,p)·T(p^{k-2}) for k ≥ 2. -/
theorem thm324_2 (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) :
    T_ad 1 ⟨p^k, ...⟩ ... = T_m ⟨p^k, ...⟩ - T_pp p * T_m ⟨p^(k-2), ...⟩

/-- Theorem 3.24(3): T(m)T(n) = ∑_{d∣gcd(m,n)} d·T(d,d)·T(mn/d²). -/
theorem thm324_3 (m n : ℕ+) :
    T_m m * T_m n =
    ∑ d in (Nat.divisors (Nat.gcd m n)).filter (· > 0),
      (d : ℤ) • (T_ad ⟨d, ...⟩ ⟨d, ...⟩ ... * T_m ⟨m * n / d^2, ...⟩)

/-- Theorem 3.24(4): T(pʳ)T(pˢ) = ∑_{i=0}^{r} pⁱ·T(pⁱ,pⁱ)·T(p^{r+s-2i})
    for r ≤ s. -/
theorem thm324_4 (p : ℕ) [hp : Fact p.Prime] (r s : ℕ) (hrs : r ≤ s) :
    T_m ⟨p^r, ...⟩ * T_m ⟨p^s, ...⟩ =
    ∑ i in Finset.range (r + 1),
      (p : ℤ)^i • (T_ad ⟨p^i, ...⟩ ⟨p^i, ...⟩ ... * T_m ⟨p^(r+s-2*i), ...⟩)

/-- Theorem 3.24(5): The recursion T(p)·T(1,pᵏ) = ... -/
theorem thm324_5 (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (hk : 0 < k) :
    T_p p * T_ad 1 ⟨p^k, ...⟩ ... =
    T_ad 1 ⟨p^(k+1), ...⟩ ... +
      if k = 1 then (p + 1 : ℤ) • T_pp p
      else (p : ℤ) • T_ad ⟨p, ...⟩ ⟨p^k, ...⟩ ...

/-- Theorem 3.24(6): deg(T(pⁱ, p^{i+k})) = p^{k-1}(p+1) for k > 0. -/
theorem thm324_6 (p : ℕ) [hp : Fact p.Prime] (i k : ℕ) (hk : 0 < k) :
    deg (GL_pair 2) (T_ad ⟨p^i, ...⟩ ⟨p^(i+k), ...⟩ ...) = p^(k-1) * (p + 1)

/-- Theorem 3.24(7): deg(T(m)) = σ₁(m) (sum of positive divisors). -/
theorem thm324_7 (m : ℕ+) :
    deg (GL_pair 2) (T_m m) = Nat.sigma 1 m
```

### Tasks

- [ ] **Step 1:** Create `GL2/Basic.lean`. Define `T_ad`, `T_m`, `T_p`, `T_pp` with notation. Define `divisorPairs m` as the finset of `(a, d)` with `a * d = m`, `a ∣ d`.
- [ ] **Step 2:** Prove basic lemmas: `T_ad_one_one = 1` (identity), `T_m_one = 1`, `T_m_prime = T_p`.
- [ ] **Step 3:** Create `GL2/MultiplicationTable.lean`.
- [ ] **Step 4:** Prove `thm324_1` (definitional).
- [ ] **Step 5:** Prove `thm324_4` — this is the core identity. Strategy: use the polynomial ring structure from Ticket 8. Embed R_p^(2) = ℤ[T(p), T(p,p)] into ℚ[A, B] via `1 - T(p)X + pT(p,p)X² = (1-AX)(1-BX)`. Then `T(pᵐ) = (A^{m+1} - B^{m+1})/(A - B)` and the product formula follows by formal algebra.
- [ ] **Step 6:** Prove `thm324_3` — follows from `thm324_4` and the coprime product theorem (Shimura 3.2.1).
- [ ] **Step 7:** Prove `thm324_5` — follows from `thm324_2` and `thm324_4`.
- [ ] **Step 8:** Prove `thm324_2` — follows from the definition of T(m) and `thm324_4` with r=0.
- [ ] **Step 9:** Prove `thm324_6` — follows from Ticket 6's degree formula.
- [ ] **Step 10:** Prove `thm324_7` — use `thm324_6`, the coprime multiplicativity of deg, and `deg(T(pᵏ)) = 1 + p + ... + pᵏ`.
- [ ] **Step 11:** Run `lake build`. Verify sorry-free.
- [ ] **Step 12:** Commit.

### Proof Strategy Notes

**For thm324_4 (the central identity):** Shimura's proof (page 63-64) embeds R_p^(2) into ℚ[A,B] via the factorization of the formal power series. In Lean, this can be done by:
1. Using the polynomial ring isomorphism from Ticket 8
2. Defining the embedding into `ℚ[A, B]` via the roots of `X² - T(p)X + pT(p,p)`
3. Computing the product formally

Alternatively, prove it by direct induction on r using identity (5), which may be simpler to formalize.

---

## Ticket 10: Hecke Operators on Modular Forms

**Status:** Not Started
**Dependencies:** Tickets 9, 1
**Assignee:** -
**Reference:** Shimura §3.4, Proposition 3.37

### Goal

Define the action of Hecke ring elements on modular forms using mathlib's `SlashAction`, and prove it's a ring homomorphism.

### Files

- Create: `LeanModularForms/HeckeRIngs/GL2/HeckeOperator.lean`

### Key Definitions

```lean
/-- The Hecke operator T(m) acting on modular forms of weight k for Γ.
    Given f ∈ M_k(Γ), T(m)f = ∑_{ad=m, a|d} ∑_{b=0}^{d-1} f |[k] [[a,b],[0,d]].

    This uses mathlib's SlashAction: f ∣[k] γ for γ ∈ GL₂(ℝ)⁺. -/
noncomputable def heckeOperator (k : ℤ) (Γ : Subgroup (SL(2, ℤ)))
    (m : ℕ+) : ModularForm Γ k →ₗ[ℂ] ModularForm Γ k

/-- More generally: any element of the Hecke ring acts on modular forms. -/
noncomputable def heckeAction (k : ℤ) (Γ : Subgroup (SL(2, ℤ))) :
    HeckeAlgebra₂ →+* Module.End ℂ (ModularForm Γ k)

/-- The action on cusp forms preserves cuspidality. -/
noncomputable def heckeOperatorCusp (k : ℤ) (Γ : Subgroup (SL(2, ℤ)))
    (m : ℕ+) : CuspForm Γ k →ₗ[ℂ] CuspForm Γ k

-- Notation
scoped notation f " |T(" m ")" => heckeOperator k Γ m f
```

### Key Theorems

```lean
/-- Shimura Proposition 3.37: the double coset action sends modular forms
    to modular forms (and cusp forms to cusp forms). -/
theorem heckeOperator_well_defined ...

/-- The action is a ring homomorphism (Shimura §3.4). -/
theorem heckeAction_ringHom :
    RingHom.comp (heckeAction k Γ) (heckeAction k Γ) = heckeAction k Γ
    -- i.e., T(m) ∘ T(n) acts the same as T(m) * T(n) in the Hecke ring

/-- Hecke operators commute (follows from commutativity of Hecke ring). -/
theorem heckeOperator_comm (m n : ℕ+) :
    heckeOperator k Γ m ∘ₗ heckeOperator k Γ n =
    heckeOperator k Γ n ∘ₗ heckeOperator k Γ m

/-- The Hecke algebra action factors through the degree map:
    deg(T(m)) = sum of coefficients in the slash expansion. -/
theorem heckeOperator_trace_eq_deg ...
```

### Tasks

- [ ] **Step 1:** Create `GL2/HeckeOperator.lean`. Import mathlib's `SlashAction`, `ModularForm`, and the GL₂ Hecke ring from Ticket 9.
- [ ] **Step 2:** Define the double coset action on functions ℍ → ℂ: for a double coset ΓαΓ = ⊔ᵢ Γαᵢ, define `f |[ΓαΓ]_k = ∑ᵢ f |[k] αᵢ`. Use the left coset decomposition from Ticket 6.
- [ ] **Step 3:** Prove independence of coset representative choice.
- [ ] **Step 4:** Prove the action preserves modular form properties (slash-invariance, holomorphy, boundedness at cusps) — this gives `heckeOperator_well_defined`.
- [ ] **Step 5:** Prove the action preserves cuspidality — gives `heckeOperatorCusp`.
- [ ] **Step 6:** Define `heckeAction` as a ring homomorphism. The key identity to verify is `(f |[Γα₁Γ]_k) |[Γα₂Γ]_k = f |[Γα₁Γ · Γα₂Γ]_k`, which follows from the associativity of the slash action and the double coset multiplication formula.
- [ ] **Step 7:** Prove `heckeOperator_comm` using `CommRing` from Ticket 5.
- [ ] **Step 8:** Define the explicit formula for `T(m)` acting on modular forms: `T(m)f(z) = m^{k-1} ∑_{ad=m, a|d} d^{-k} ∑_{b=0}^{d-1} f((az+b)/d)`. Prove equivalence with the abstract definition.
- [ ] **Step 9:** Run `lake build`. Verify sorry-free.
- [ ] **Step 10:** Commit.

### Important Notes for Workers

- Mathlib's `SlashAction` uses `GL (Fin 2) ℝ` (or `SL(2, ℤ)`) acting on `ℍ → ℂ`. We need to embed our integer matrices into `GL (Fin 2) ℝ` to use the slash action.
- The formula `f |[k] γ = det(γ)^{k/2-1} · f(γ(z)) · j(γ,z)^{-k}` is in `Mathlib.NumberTheory.ModularForms.SlashActions`.
- The existing file `LeanModularForms/ForMathlib/SlashActions.lean` has additional slash action lemmas we should use.
- The well-definedness proof (Step 4) is the hardest part: showing that ∑ f|[k]αᵢ is still slash-invariant under Γ. This uses the fact that left-multiplying by γ ∈ Γ permutes the coset representatives.

---

## Appendix A: Shimura Reference Map

| Plan Item | Shimura Reference | Page |
|-----------|------------------|------|
| Degree map | Proposition 3.3 | 52 |
| Anti-involution commutativity | Proposition 3.8 | 56 |
| GL_n setup | §3.2, Lemma 3.10 | 55-56 |
| Diagonal representatives | Elementary divisor theorem | 56 |
| Coset decomposition | §3.2, implied by Prop 3.14 | 57 |
| Degree formula | Propositions 3.14, 3.18 | 57-58 |
| Coprime product | Proposition 3.16 | 57 |
| Scalar multiplication | Proposition 3.17 | 58 |
| Prime decomposition | §3.2 (page 58) | 58 |
| Polynomial ring | Theorem 3.20 | 59-60 |
| Euler product | Theorem 3.21 | 61 |
| n=2 identities | Theorem 3.24 | 63 |
| Hecke operator action | §3.4, Proposition 3.37 | 73 |

## Appendix B: Mathlib Dependencies

| Feature | Mathlib Module |
|---------|---------------|
| GL_n(ℚ) | `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs` |
| SL_n(ℤ) | `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup` |
| Diagonal matrices | `Mathlib.Data.Matrix.Diagonal` |
| Determinants | `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` |
| Commensurator | `Mathlib.GroupTheory.Commensurable` |
| Double cosets | `Mathlib.GroupTheory.DoubleCoset` |
| Slash action | `Mathlib.NumberTheory.ModularForms.SlashActions` |
| Modular forms | `Mathlib.NumberTheory.ModularForms.Basic` |
| Finsupp | `Mathlib.Data.Finsupp.Basic` |

## Appendix C: Progress Update Protocol

When finishing work on any ticket, update the Progress Tracker table at the top of this document:

1. Change **Status** to `Done` (or `In Progress` / `Blocked`)
2. Add your name/identifier to **Assignee**
3. If blocked, add a note explaining what's blocking
4. List any new helper lemmas you introduced that other tickets should know about
5. If the sorry count changed, note it

**Convention for partial progress:** If a ticket is partially done, mark it `In Progress` and add a sub-table listing which steps are done. Example:
```
| **4** | Diagonal Representatives | In Progress | Worker-B | 3 | Steps 1-3 done, Step 4 (SNF) in progress |
```
