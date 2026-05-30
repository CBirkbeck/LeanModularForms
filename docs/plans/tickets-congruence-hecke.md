# Tickets: Congruence Subgroup Hecke Algebra (Shimura §3.3)

## Goal

Fill all sorries in `GLn/CongruenceHecke.lean` and `GLn/Basic.lean` (Lemma 3.10),
establishing that the level-N Hecke algebra is a quotient of the level-1 algebra.

**File**: `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke.lean` (4635 lines)

## Progress (as of 2026-04-02)

| Ticket | Status | Description |
|--------|--------|-------------|
| T1 | ✅ DONE | Lemma 3.10: `commensurator_SLnZ_eq_top` |
| T2 | ✅ DONE | Δ₀(N) submonoid: `one_mem'`, `mul_mem'` |
| T3 | ✅ DONE | Foundation lemmas 3.28-3.29 (SL2Surjection.lean bypassed S1) |
| T4 | ✅ DONE | `Gamma0_le_Delta0` |
| T5 | ✅ DONE | `Delta0_le_commensurator` |
| T6 | ✅ DONE | `Gamma0_pair` valid |
| T7 | ✅ DONE | Prop 3.30 (`shimura_prop_3_30`) |
| T8 | ✅ DONE | Prop 3.31 (`shimura_prop_3_31`) |
| T9 | ✅ DONE | Props 3.32-3.33 (double coset structure) |
| T10 | ⚠️ 1 sorry | Thm 3.35: `ψ_surjective` at line 4591 |

**2 sorries remain** (down from 14 original):
1. Line 3785: `T_bad_mul_aux_card_bij` — cardinality bijection for bad-level multiplication
2. Line 4591: `ψ_surjective` — Shimura Thm 3.34 generator surjectivity (**blocks Thm 3.35**)

**Previous hard blockers resolved**: S1 (strong approximation) was bypassed via
`SL2Surjection.lean` (244 lines, 0 sorries). All of T3-T9 completed since 2026-03-28.
#1 needs explicit witness construction using commensurability.
#3 needs strong approximation (surjectivity of SL₂(ℤ) → SL₂(ℤ/dℤ)).

## Dependency Graph

```
T1 (Lemma 3.10) ──────────┐
                           ▼
T2 (Δ₀(N) submonoid) ──→ T4 (Γ₀(N) ≤ Δ₀(N))
                           │
T3 (Lemma 3.28-3.29) ──→ T5 (Δ₀(N) ≤ commensurator)
                           │
                           ▼
                     T6 (Gamma0_pair)  ← already defined, needs T4+T5
                           │
T7 (Prop 3.30) ───────────┤
                           │
T8 (Prop 3.31) ───────────┤
                           │
T9 (Prop 3.32-3.33) ──────┤
                           ▼
                     T10 (Thm 3.35: surjection)
```

**Parallel work possible**: T1, T2, T3 can all be done simultaneously.
T7 and T8 can be done simultaneously once T6 is done.

---

## T1: Shimura Lemma 3.10 — commensurator(SLₙ(ℤ)) = GLₙ(ℚ)

**File**: `GLn/Basic.lean`
**Sorry**: `commensurator_SLnZ_eq_top`
**Can run in parallel with**: T2, T3

### Statement
```
commensurator (SLnZ_subgroup n) = ⊤
```

### Proof outline (Shimura p.55-56)
1. Let α ∈ GLₙ(ℚ). Write α = cβ with c ∈ ℚ, β ∈ Mₙ(ℤ).
2. Then αΓα⁻¹ = βΓβ⁻¹.
3. By Lemma 3.9 (which we need to prove or use existing API):
   Γ_b ⊂ β⁻¹Γ_N β ∩ β Γ_N β⁻¹ where b = det(β).
4. Since [Γ : Γ_b] < ∞, we get [Γ : Γ ∩ αΓα⁻¹] < ∞.
5. Substituting α⁻¹ for α: [αΓα⁻¹ : αΓα⁻¹ ∩ Γ] < ∞.
6. Therefore α ∈ commensurator(Γ).

### Dependencies
- Lemma 3.9 (`Γ_Nb ⊂ β⁻¹Γ_N β`): We essentially have this in our
  `posDetInt_le_commensurator` proof (the congruence subgroup Γ(d) argument).
  Extract and generalize.
- Our existing proof of `posDetInt_le_commensurator` already does this for
  α ∈ posDetInt. Need to extend to all of GLₙ(ℚ) by the c·β decomposition.

### Estimated effort: Medium

---

## T2: Δ₀(N) submonoid — closure under multiplication

**File**: `GLn/CongruenceHecke.lean`
**Sorry**: `Delta0_submonoid.one_mem'`, `Delta0_submonoid.mul_mem'`
**Can run in parallel with**: T1, T3

### Statement
The set `{g ∈ GL₂(ℚ) | int entries, det > 0, N | c, (a, N) = 1}` is a submonoid.

### Proof outline
- **one_mem'**: The identity matrix has a=d=1, b=c=0. Check: N | 0, gcd(1,N)=1.
- **mul_mem'**: If A = [a₁ b₁; c₁ d₁] and B = [a₂ b₂; c₂ d₂] with N | c₁, N | c₂,
  gcd(a₁,N) = 1, gcd(a₂,N) = 1, then AB = [a₁a₂+b₁c₂, ...; c₁a₂+d₁c₂, ...].
  - N | (c₁a₂ + d₁c₂) since N | c₁ and N | c₂.
  - gcd(a₁a₂+b₁c₂, N) = 1: since N | c₂, a₁a₂+b₁c₂ ≡ a₁a₂ (mod N),
    and gcd(a₁a₂, N) = 1 since gcd(a₁,N) = gcd(a₂,N) = 1.
  - Int entries: product of integer matrices.
  - det > 0: product of positive determinants.

### Estimated effort: Easy

---

## T3: Lemma 3.28 and Lemma 3.29 — foundational congruence lemmas

**File**: `GLn/CongruenceHecke.lean` (new lemmas before the pair definition)
**Can run in parallel with**: T1, T2

### Lemma 3.28 (Shimura p.66)
```
Γ_c = Γ_a · Γ_b   when c = gcd(a, b)
```
where Γ_N = {γ ∈ Γ | γ ≡ 1 mod N} is the principal congruence subgroup.

**Proof**: By CRT, if α ∈ Γ_c, there exists β ∈ Mₙ(ℤ) with β ≡ 1 mod a,
β ≡ α mod b, det(β) ≡ 1 mod ab/c. Then γ such that α = γ·τ⁻¹·α gives
τ ∈ Γ_a, γ⁻¹α ∈ Γ_b.

### Lemma 3.29 (Shimura p.66)
For α, β ∈ Δ_N:
1. Γ'αΓ' = {ξ ∈ ΓαΓ | λ_N(ξ) ∈ λ_N(Γ'α)} if α ∈ Φ.
2. Γ_NαΓ_N = Γ_NβΓ_N iff ΓαΓ = ΓβΓ and α ≡ β mod N.
3. ΓαΓ = Γ'αΓ' (double cosets agree for Γ and Γ' when α ∈ Φ).
4. Γ'αΓ' = Γ_NαΓ_N if α ∈ Φ.
5. If α ∈ Φ and Γ'αΓ' = ∪ᵢ Γ'αᵢ (disjoint), then ΓαΓ = ∪ᵢ Γαᵢ (disjoint).

**Proof (for (3))**: Put a = det(α). By Lemma 3.28 and 3.9,
Γ_a·Γ_N ⊂ α⁻¹ΓαΓ_N, so α⁻¹ΓαΓ ⊂ α⁻¹ΓαΓ. The opposite inclusion is obvious.
The rest follow from (1) and (3).

### Estimated effort: Medium-Hard (most technical ticket)

---

## T4: Γ₀(N) ≤ Δ₀(N)

**File**: `GLn/CongruenceHecke.lean`
**Sorry**: `Gamma0_le_Delta0`
**Depends on**: T2

### Statement
```
((Gamma0 N).map (mapGL ℚ)).toSubmonoid ≤ Delta0_submonoid N
```

### Proof outline
Let γ ∈ Γ₀(N), so γ = [a b; cN d] ∈ SL₂(ℤ) with N | c-entry. Then:
- mapGL ℚ γ has integer entries (from the SL₂(ℤ) embedding)
- det = 1 > 0
- The (1,0) entry is cN, so N | (cN) ✓
- The (0,0) entry is a. Since ad - bcN = 1, we have gcd(a, N) = 1 ✓

### Estimated effort: Easy

---

## T5: Δ₀(N) ≤ commensurator(Γ₀(N))

**File**: `GLn/CongruenceHecke.lean`
**Sorry**: `Delta0_le_commensurator`
**Depends on**: T1 (or can use existing `posDetInt_le_commensurator` + finite index)

### Statement
```
Delta0_submonoid N ≤ (commensurator ((Gamma0 N).map (mapGL ℚ))).toSubmonoid
```

### Proof outline
Two approaches:

**Approach A** (using T1): Since Δ₀(N) ⊂ posDetInt ⊂ GLₙ(ℚ) = commensurator(SLₙ(ℤ))
(by Lemma 3.10), and Γ₀(N) has finite index in SL₂(ℤ), commensurability with
SL₂(ℤ) implies commensurability with Γ₀(N).

**Approach B** (direct, without T1): For α ∈ Δ₀(N), show that Γ₀(N) ∩ αΓ₀(N)α⁻¹
has finite index in both Γ₀(N) and αΓ₀(N)α⁻¹. Use the congruence subgroup
Γ(d·N) ⊂ Γ₀(N) ∩ αΓ₀(N)α⁻¹ where d = det(α), adapting our existing
`posDetInt_le_commensurator` proof.

### Estimated effort: Medium (Approach B avoids needing T1)

---

## T6: Gamma0_pair is valid

**File**: `GLn/CongruenceHecke.lean`
**Status**: Already defined, compiles with T4+T5 as sorries.
**Depends on**: T4, T5

No new work needed — this is just the `HeckePair` constructor applied to T4 and T5.

---

## T7: Shimura Proposition 3.30 — the homomorphism R(Γ', Φ) → R(Γ, Δ)

**File**: `GLn/CongruenceHecke.lean`
**Sorry**: `shimura_prop_3_30`
**Depends on**: T6
**Can run in parallel with**: T8

### Statement
The correspondence Γ'αΓ' ↦ ΓαΓ defines a ring homomorphism R(Γ', Φ) → R(Γ, Δ).

### Proof outline (Shimura p.67)
1. By Lemma 3.29(5), if Γ'αΓ' = ∪ᵢ Γ'αᵢ and Γ'βΓ' = ∪ⱼ Γ'βⱼ are disjoint,
   then ΓαΓ = ∪ᵢ Γαᵢ and ΓβΓ = ∪ⱼ Γβⱼ are also disjoint.
2. The product (Γ'αΓ')(Γ'βΓ') = Σ_ξ c_ξ(Γ'ξΓ') with c_ξ = #{(i,j) | Γ'αᵢβⱼ = Γ'ξ}.
3. By 3.29, Γ'ξΓ' ↦ ΓξΓ, and the map Γ'ξΓ' ↦ ΓξΓ is one-to-one (since
   λ_N(Γ'α) = λ_N(Γ'β) implies the same coset relation).
4. The coefficients c_ξ match: #{(i,j) | Γαᵢβⱼ = Γξ} = #{(i,j) | Γ'αᵢβⱼ = Γ'ξ}
   by the disjointness from step 1.

### Key sublemma needed
Lemma 3.29(5): the coset decomposition of Γ'αΓ' refines to ΓαΓ.

### Estimated effort: Hard

---

## T8: Shimura Proposition 3.31 — the isomorphism R(Γ', Δ'_N) ≅ R(Γ, Δ_N)

**File**: `GLn/CongruenceHecke.lean`
**Sorry**: `shimura_prop_3_31`
**Depends on**: T6, T7
**Can run in parallel with**: T7

### Statement
R(Γ', Δ'_N) ≅ R(Γ, Δ_N) via the map Γ'αΓ' ↦ ΓαΓ.

### Proof outline (Shimura p.67-68)
1. By Prop 3.30, the map is a homomorphism. Need surjectivity and injectivity.
2. **Surjectivity**: Let η ∈ Δ_N with b = det(η). Take integer c with bc ≡ 1 mod N,
   put φ = [1 0; 0 c]. Then τ ≡ ηφ mod N, so τ⁻¹η ∈ Δ*_N, and ΓαΓ = Γτ⁻¹ηΓ.
3. **Injectivity**: If ΓαΓ = ΓβΓ with α ≡ [1 0; 0 c], β ≡ [1 0; 0 d] mod N,
   then c ≡ det(α) = det(β) ≡ d mod N. By 3.29(1), Γ'αΓ' = Γ'βΓ'.
4. R(Γ, Δ_N) is a free ℤ-module generated by ΓαΓ with α ∈ Δ*_N.

### Estimated effort: Medium

---

## T9: Propositions 3.32–3.33 — double coset structure at level N

**File**: `GLn/CongruenceHecke.lean` (new lemmas)
**Depends on**: T3, T6
**Can run in parallel with**: T7, T8

### Proposition 3.32 (Shimura p.68-70)
For α ∈ Δ' with det(α) = mq, m | N^∞, (q,N) = 1:
1. Γ'αΓ' = {β ∈ Δ' | det(β) = mq, E_p β E_p = E_p α E_p for all p | q}
2. There exists ξ ∈ Δ*_N with det(ξ) = q and E_p ξ E_p = E_p α E_p for all p | q.
3. If ξ is as in (2) and η = [1 0; 0 m], then Γ'αΓ' = (Γ'ξΓ')·(Γ'ηΓ').
4. ξ can be taken from Δ*_N.

**Proof**: Long but follows from the p-adic elementary divisor theory and CRT.

### Proposition 3.33 (Shimura p.70)
For α ∈ Δ' with det(α) = m, m | N^∞:
```
Γ'αΓ' = {β ∈ Δ' | det(β) = m} = ∪_{r=0}^{m-1} Γ'[1 tr; 0 m]   (disjoint)
```

**Proof**: Special case of Prop 3.32. The coset representatives are [1 r; 0 m] for 0 ≤ r < m.

### Estimated effort: Hard (most technical, but not blocking for T10)

---

## T10: Shimura Theorem 3.35 — the surjection

**File**: `GLn/CongruenceHecke.lean`
**Sorry**: `shimura_thm_3_35`
**Depends on**: T7, T8, T9

### Statement
```
∃ φ : 𝕋 (GL_pair 2) ℤ →+ 𝕋 (Gamma0_pair N) ℤ, Function.Surjective φ
```

### Proof outline (Shimura p.71)
1. By Prop 3.32, every Γ'αΓ' with α ∈ Δ' factors as (Γ'ξΓ')·(Γ'ηΓ')
   with ξ ∈ Δ*_N and η = [1 0; 0 m] with m | N^∞.
2. By Prop 3.31, R(Γ', Δ'_N) ≅ R(Γ, Δ_N). Under this isomorphism,
   T'(a,d) with (d,N) = 1 corresponds to T(a,d).
3. The elements T'(p) for p | N are just Γ'[1 0; 0 p]Γ' with the simple
   coset decomposition from Prop 3.33.
4. Define the surjection by:
   - T(n) ↦ T'(n) (image under the coset correspondence)
   - T(p,p) ↦ T'(p,p) for p ∤ N (via the isomorphism of step 2)
   - T(p,p) ↦ 0 for p | N
5. **Key computation**: pT'(p,p) = T'(p)² - T'(p²) for p ∤ N. This follows from
   applying Prop 3.31 to our existing identity pT(p,p) = T(p)² - T(p²) (Thm 3.24).
6. For p | N: T'(p^k) = T'(p)^k since the only coset representatives are
   [1 r; 0 p^k] and the multiplication is T'(p)·T'(p^{k-1}) = T'(p^k) by Prop 3.33.
7. **Surjectivity**: R(Γ', Δ') is generated by T'(p) for p | N and T'(1,p), T'(p,p)
   for p ∤ N (Thm 3.34). The first are images of T(p), the others are images under
   the isomorphism from T(1,p) and T(p,p).

### Estimated effort: Medium-Hard (putting together T7-T9)

---

## Summary

| Ticket | Description | Shimura | Depends | Parallel | Effort |
|--------|-----------|---------|---------|----------|--------|
| **T1** | Lemma 3.10: commensurator = GLₙ(ℚ) | Lemma 3.10 | — | T2, T3 | Medium |
| **T2** | Δ₀(N) submonoid closure | (3.3.1) | — | T1, T3 | Easy |
| **T3** | Lemma 3.28-3.29 foundations | L.3.28, L.3.29 | — | T1, T2 | Medium-Hard |
| **T4** | Γ₀(N) ≤ Δ₀(N) | — | T2 | T5 | Easy |
| **T5** | Δ₀(N) ≤ commensurator | L.3.10 | T1 or direct | T4 | Medium |
| **T6** | Gamma0_pair valid | §3.3 | T4, T5 | — | Done |
| **T7** | Prop 3.30: homomorphism | Prop 3.30 | T3, T6 | T8 | Hard |
| **T8** | Prop 3.31: isomorphism | Prop 3.31 | T6, T7 | T7 | Medium |
| **T9** | Prop 3.32-3.33: structure | Prop 3.32-33 | T3, T6 | T7, T8 | Hard |
| **T10** | Thm 3.35: surjection | Thm 3.35 | T7, T8, T9 | — | Medium-Hard |

### Parallel execution plan

**Wave 1** (independent): T1 + T2 + T3

**Wave 2** (after T2): T4

**Wave 2'** (after T1 or direct): T5

**Wave 3** (after T4+T5): T6 (already done), then T7 + T8 in parallel

**Wave 4** (after T3+T6): T9

**Wave 5** (after T7+T8+T9): T10
