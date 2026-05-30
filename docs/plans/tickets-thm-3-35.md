# Plan: Shimura Theorem 3.35 (The Last Sorry)

## Goal

Prove the surjective ring homomorphism R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N)).

## Dependencies (what we need to prove)

### Prop 3.33 (Explicit cosets for N-power det)

**Statement**: For α ∈ Δ' with det(α) = m where m | N^∞:

```
Γ'αΓ' = {β ∈ Δ' | det(β) = m} = ∪_{r=0}^{m-1} Γ'[1, tr; 0, m]  (disjoint)
```

where t is a fixed integer with (t, N) = 1.

**Key consequences**:
- All elements of Δ' with the same N-power determinant are in the same Γ'-double coset
- deg(T'(m)) = m when m | N^∞
- T'(p^k) = T'(p)^k when p | N (since the coset [1,0;0,p^k] is the product of k copies)

**Proof outline** (Shimura p.70):
- The case q = 1 in Prop 3.32 gives the first equality
- For the second: β ∈ Δ' with det(β) = m, consider δγβ = ξ[1,tb;0,m]
  with ξ ∈ Γ_N, integer b, and elements γ, δ of Γ'.
  Write b = mh + r with 0 ≤ r < m, then [1,tb;0,m] = [1,th;0,1][1,tr;0,m]
- Disjointness: if [1,tr;0,m] and [1,ts;0,m] are in the same Γ'-left coset,
  then γ[1,tr;0,m] = [1,ts;0,m] with γ = [a,tb;c,d] ∈ Γ', giving γ = 1.

### Prop 3.32 (Factorization of double cosets)

**Statement**: For α ∈ Δ' with det(α) = mq where m | N^∞ and (q,N) = 1:

```
Γ'αΓ' = (Γ'ξΓ') · (Γ'ηΓ')
```

where det(ξ) = q, η = [1,0;0,m], and ξ can be taken from Δ*_N.

**Proof outline** (Shimura p.68-70):
1. Define X(α) = {β ∈ Δ' | det(β) = mq, E_p βE_p = E_p αE_p for all p | q}
2. Clearly Γ'αΓ' ⊂ X(α)
3. Find ξ ∈ Δ*_N with det(ξ) = q using CRT on the p-adic elementary divisors
4. Show β ∈ Γ'ξηΓ' for all β ∈ X(α) using the Chinese remainder theorem
5. The product (Γ'ξΓ')·(Γ'ηΓ') has multiplicity 1 (the coset decomposition is bijective)

### Thm 3.34 (Generation)

**Statement**: R(Γ', Δ') is generated as a ℤ-algebra by:
- T'(p) for all primes p dividing N
- T'(1,p) and T'(p,p) for all primes p not dividing N

**Proof**: From Props 3.32-3.33 + Prop 3.31 + the coprime multiplication.

### Thm 3.35 (The surjection)

**Proof**: Since R(Γ, Δ) is a polynomial ring in T(p), T(p,p) (our Thm 3.20),
define φ on generators:
- φ(T(p)) = T'(p) for all p
- φ(T(p,p)) = T'(p,p) for p ∤ N
- φ(T(p,p)) = 0 for p | N

This extends to a ring hom (polynomial ring = free). Surjective by Thm 3.34.

## Execution Plan

**Approach**: Bottom-up, proving 3.33 → 3.32 → 3.34 → 3.35.

### Step 1: Prop 3.33 (concrete, explicit)

State and prove that for m | N^∞, the Gamma0 double coset of diag(1,m) consists
of exactly m left cosets with upper-triangular representatives [1,r;0,m].

This is a direct matrix computation:
- [1,r;0,m] ∈ Δ₀(N) since gcd(1,N) = 1 and N | 0 ✓
- det([1,r;0,m]) = m ✓
- Left coset decomposition: Γ₀(N)[1,r;0,m] for distinct r are distinct
- Every β with det = m and β ∈ Δ₀(N) is in some such left coset

### Step 2: Prop 3.32 (uses CRT)

The factorization uses the same p-adic elementary divisor theory we already
have in DiagonalCosets.lean. The key new ingredient: the CRT combines the
coprime-det part ξ (which corresponds to a GL_pair coset via Prop 3.31) with
the N-power part η = [1,0;0,m].

### Step 3: Thm 3.34 (generation, combines 3.32-3.33 with existing results)

Show every Gamma0 double coset is a product of:
- Powers of T'(p) for p | N (from Prop 3.33)
- Coprime-det cosets T'(a,d) with (d,N)=1 (from Prop 3.31)
- These are products of T'(1,p), T'(p,p) (from our existing Thm 3.24)

### Step 4: Thm 3.35 (the ring hom, uses polynomial ring + 3.34)

Define the ring hom using `MvPolynomial.eval₂Hom` and our `R_p_isPolynomialRing`.
Prove surjectivity using Thm 3.34.

## Parallel Work

Steps 1 and 2 are the foundation and should be done sequentially (3.33 first, then 3.32).
Steps 3 and 4 can potentially be parallelized once 3.32 is done.
