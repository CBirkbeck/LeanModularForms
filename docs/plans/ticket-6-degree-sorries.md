# Ticket 6: Proof Plan for Degree Sorries

Two sorries remain in `GLn/Degree.lean`:
- `upperTriRep_card_le_T'_deg` (general n)
- `T'_deg_T_diag_two_prime` (n = 2)

## Files

| File | Content |
|------|---------|
| `GLn/CongruenceIndex.lean` (new) | Γ₀(pᵏ) index computation, connection to H∩αHα⁻¹ |
| `GLn/Degree.lean` (existing) | Both sorry fills, δ-opacity lemma, d=e lemma |

## Mathlib infrastructure used (do not redefine)

| What | Location | API |
|------|----------|-----|
| `Gamma0 N` | `Mathlib.NumberTheory.ModularForms.CongruenceSubgroups` | `Subgroup SL(2,ℤ)`, membership: `(A 1 0 : ZMod N) = 0` |
| `instFiniteIndexGamma0` | same | `(Gamma0 N).FiniteIndex` when `[NeZero N]` |
| `Gamma0Map N` | same | `Gamma0 N →* ZMod N` (maps σ ↦ σ₁₁ mod N) |
| `SpecialLinearGroup.transpose` | `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup` | `Aᵀ : SL(n, R)` |
| `Matrix.diagonal_transpose` | `Mathlib.Data.Matrix.Diagonal` | `(diagonal v)ᵀ = diagonal v` |
| `Matrix.transpose_mul` | mathlib | `(A * B)ᵀ = Bᵀ * Aᵀ` |
| `Subgroup.index` | `Mathlib.GroupTheory.Index` | `H.index = Nat.card (G ⧸ H)` |
| `relIndex_mul_index` | same | `H.relIndex K * K.index = H.index` when `H ≤ K` |
| `Subgroup.relIndex_pointwise_smul` | same | `(h • J).relIndex (h • K) = J.relIndex K` |
| `Nat.card_eq_fintype_card` | `Mathlib.SetTheory.Cardinal.Finite` | converts between the two card notions |
| `Fintype.card_le_of_injective` | `Mathlib.Data.Fintype.Card` | `Injective f → card α ≤ card β` |
| `ModularGroup.S`, `ModularGroup.T` | `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup` | generators of SL₂(ℤ) |
| `ModularGroup.coe_T_zpow` | same | `(T ^ n).1 = !![1, n; 0, 1]` |
| `ZMod.intCast_zmod_eq_zero_iff_dvd` | mathlib | `(a : ZMod n) = 0 ↔ (n : ℤ) ∣ a` |

## Shared infrastructure

### S1. δ-opacity: T'_deg depends only on the double coset

```lean
lemma T'_deg_eq_of_doubleCoset (P : ArithmeticGroupPair G) (D : T' P)
    (α : P.Δ) (hα : D.set = DoubleCoset.doubleCoset α P.H P.H) :
    T'_deg P D = Nat.card (P.H ⧸ (ConjAct.toConjAct (α : G) • P.H).subgroupOf P.H)
```

**Proof**: Extract δ = D.eql.choose. From D.eql.choose_spec and hα, δ ∈ HαH,
so δ = h₁·α·h₂ for h₁, h₂ ∈ H. Then ConjAct.toConjAct δ • H =
(ConjAct.toConjAct h₁) • (ConjAct.toConjAct α • H). Since h₁ ∈ H,
use `relIndex_pointwise_smul` to show the subgroupOf and its index
are preserved. Convert via `Nat.card_eq_fintype_card`.

### S2. d = e for diagonal matrices (general n)

```lean
lemma index_conj_eq_index_conj_inv_of_diag (n : ℕ) [NeZero n] (a : Fin n → ℕ+) :
    Nat.card (SLnZ_subgroup n ⧸
      (ConjAct.toConjAct (diagMat n a)⁻¹ • SLnZ_subgroup n).subgroupOf (SLnZ_subgroup n)) =
    Nat.card (SLnZ_subgroup n ⧸
      (ConjAct.toConjAct (diagMat n a) • SLnZ_subgroup n).subgroupOf (SLnZ_subgroup n))
```

**Proof via transpose** (general n):

1. The map τ : SL(n, ℤ) → SL(n, ℤ) given by `SpecialLinearGroup.transpose` is an involution.
2. For diagonal α: αᵀ = α by `Matrix.diagonal_transpose`.
3. τ sends H ∩ α⁻¹Hα to H ∩ αHα⁻¹:
   - If σ ∈ SL_n(ℤ) and α⁻¹σα ∈ SL_n(ℤ), then (α⁻¹σα)ᵀ = αᵀσᵀ(α⁻¹)ᵀ = ασᵀα⁻¹
   - Uses: `Matrix.transpose_mul`, `Matrix.diagonal_transpose`
4. τ is bijective (involution), so the two subgroups have equal index.

## Sorry 1: `upperTriRep_card_le_T'_deg` (general n)

**Chain**:
```
card(UpperTriRep)
  ≤ Nat.card (H ⧸ (H ∩ α⁻¹Hα))    -- injection into right cosets [Step 1]
  = Nat.card (H ⧸ (H ∩ αHα⁻¹))      -- d = e [S2]
  = T'_deg                            -- δ-opacity [S1]
```

### Step 1: UpperTriReps inject into right cosets

Each `upperTriGL B ∈ H·diagMat·H` (by `upperTriGL_mem_doubleCoset`).
Decompose: `upperTriGL B = hB · diagMat · kB` with hB, kB ∈ H.

Map B to the coset [kB] in H/(H ∩ α⁻¹Hα). Injectivity follows from
`upperTriMat_distinct_cosets`: if B₁ ≠ B₂ then they're in distinct
right cosets of H, so [kB₁] ≠ [kB₂].

Apply `Fintype.card_le_of_injective` to get card(UpperTriRep) ≤ d.
Then S2 gives d = e and S1 gives e = T'_deg.

## Sorry 2: `T'_deg_T_diag_two_prime` (n = 2)

**Chain**:
```
T'_deg (GL_pair 2) (T_diag 2 a hdiv)
  = Nat.card (H ⧸ (H ∩ αHα⁻¹))       -- δ-opacity [S1]
  = (Gamma0 (p^k)).index               -- conjugation = Gamma0 [C1]
  = p^{k-1} * (p + 1)                  -- index formula [C4]
```

### C1: H ∩ αHα⁻¹ corresponds to Gamma0(pᵏ)

For σ ∈ SL₂(ℤ), the conjugate α⁻¹σα has (i,j) entry (aⱼ/aᵢ)·σᵢⱼ.
The (1,0) entry has factor a₀/a₁ = 1/pᵏ, requiring pᵏ | σ₁₀.
All other entries are automatically integers. This matches
`Gamma0_mem`: `(σ 1 0 : ZMod (p^k)) = 0`.

The injective `SLnZ_to_GLnQ` transfers the index.

### C2: Base case `(Gamma0 p).index = p + 1`

```lean
lemma Gamma0_prime_index (p : ℕ) (hp : Nat.Prime p) :
    (Gamma0 p).index = p + 1
```

Representatives for left cosets of Γ₀(p) in SL₂(ℤ):

| Rep | Matrix | Left column mod p | ℙ¹ point |
|-----|--------|-------------------|----------|
| I | [[1,0],[0,1]] | (1, 0)ᵀ | [1:0] |
| T^j · S (j=0..p-1) | [[j,-1],[1,0]] | (j, 1)ᵀ | [j:1] |

**Distinctness**: (T^{j₁}·S)⁻¹·(T^{j₂}·S) = [[1,0],[j₁-j₂,1]].
The (1,0) entry j₁-j₂ is in Γ₀(p) iff p | (j₁-j₂). ✓

**Exhaustiveness**: For σ ∈ SL₂(ℤ):
- If p | σ₁₀: σ ∈ Γ₀(p), coset of I.
- If p ∤ σ₁₀: set j ≡ σ₀₀·σ₁₀⁻¹ mod p. Then σ is in coset of T^j·S.

### C3: Inductive step `(Gamma0 (p^(k+1))).relIndex (Gamma0 (p^k)) = p`

```lean
lemma Gamma0_relindex_step (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k) :
    (Gamma0 (p ^ (k+1))).relIndex (Gamma0 (p^k)) = p
```

Representatives: σ_c = [[1,0],[c·pᵏ,1]] for c = 0,...,p-1.

- Each σ_c ∈ Γ₀(pᵏ) since pᵏ | c·pᵏ. ✓
- σ_{c₁}⁻¹·σ_{c₂} = [[1,0],[(c₂-c₁)·pᵏ,1]], in Γ₀(p^{k+1}) iff p | (c₂-c₁). ✓
- Exhaustive: For σ ∈ Γ₀(pᵏ), set c ≡ (σ₁₀/pᵏ)·σ₁₁⁻¹ mod p. Then σ·σ_c⁻¹ ∈ Γ₀(p^{k+1}). ✓

### C4: Full index formula

```lean
lemma Gamma0_prime_power_index (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k) :
    (Gamma0 (p ^ k)).index = p ^ (k - 1) * (p + 1)
```

Induction on k using `relIndex_mul_index`:
- Base k=1: (Gamma0 p).index = p+1 = p⁰·(p+1). [C2]
- Step k→k+1: index = relIndex · index(Gamma0 pᵏ) = p · pᵏ⁻¹(p+1). [C3 + IH]

## Dependency graph

```
Matrix.diagonal_transpose ─┐
SL.transpose ───────────────┤
Matrix.transpose_mul ───────┴─► [S2] d = e (general n)
                                         │
relIndex_pointwise_smul ──► [S1] δ-opacity │
                                 │       │
upperTriMat_distinct_cosets ──┐  │       │
card_le_of_injective ─────────┤  │       │
                               ▼  ▼       ▼
                        [Sorry 1] card ≤ T'_deg  (general n)

Gamma0 (mathlib) ──────────────► [C1] H∩αHα⁻¹ = Gamma0
ModularGroup.S, .T ────────────► [C2] index(Γ₀(p)) = p+1
                                 [C3] relindex step = p
relIndex_mul_index (mathlib) ───► [C4] index(Γ₀(pᵏ)) = pᵏ⁻¹(p+1)
                                         │
                          [S1] ──────────┤
                                         ▼
                                 [Sorry 2] T'_deg = pᵏ⁻¹(p+1)
```

## Implementation order

1. **S1** (δ-opacity) — needed by both sorries
2. **C1–C4** (CongruenceIndex.lean) — needed by Sorry 2
3. **Sorry 2** fill — higher priority for downstream Theorem 3.24
4. **S2** (d = e via transpose) — needed by Sorry 1
5. **Sorry 1** fill
