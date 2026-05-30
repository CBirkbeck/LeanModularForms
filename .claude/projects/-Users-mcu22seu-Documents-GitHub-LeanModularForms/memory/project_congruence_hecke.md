---
name: Congruence Subgroup Hecke Algebra Progress
description: Status of Shimura §3.3 formalization — Hecke ring for congruence subgroups, 1 sorry remaining
type: project
---

## Congruence Hecke Algebra (Shimura §3.3) — as of 2026-03-29

### Files created
- `GLn/CongruenceHecke.lean` (947 lines, 1 sorry)
- `GLn/SL2Surjection.lean` (244 lines, 0 sorries)

### Fully proved (sorry-free)
- **Lemma 3.10**: `commensurator_SLnZ_eq_top` — commensurator(SLₙ(ℤ)) = GLₙ(ℚ)
- **Δ₀(N) submonoid**: `one_mem'`, `mul_mem'` closure
- **Γ₀(N) ≤ Δ₀(N)**: `Gamma0_le_Delta0`
- **Δ₀(N) ≤ commensurator**: `Delta0_le_commensurator` (via `Commensurable.eq` + finite index)
- **Gamma0_pair**: valid HeckePair for (Γ₀(N), Δ₀(N))
- **SL₂ surjectivity**: `SL2_reduction_surjective` — SL₂(ℤ) → SL₂(ℤ/dℤ) surjective
- **Coprime lifting**: `IsCoprime.lift_to_int` — lift coprime from ZMod to ℤ (Euclidean descent)
- **Lemma 3.28**: `Gamma_gcd_eq_mul` — Γ(gcd(a,b)) = Γ(a) ⊔ Γ(b) (via SL₂ surjectivity + CRT)
- **Lemma 3.29(3)**: `doubleCoset_eq_of_Gamma0_coprimeDet` — ΓαΓ ∩ Δ₀(N) = Γ₀(N)αΓ₀(N)
- **Prop 3.30**: `shimura_prop_3_30` — cosetMap as AddMonoidHom via Finsupp.mapDomain
- **Prop 3.31**: `shimura_prop_3_31` — cosetMap injective on coprime-det cosets

### 4 sorries remaining (all sub-lemmas of the proved Thm 3.35 architecture)
- `instCommRing_Gamma0` (line 914) — CommRing for Gamma0_pair, needs anti-involution
- `prod_removePrime_lt` (line 958) — number theory: removing p-component decreases product
- `ker_π_le_ker_ψ` (line 1020) — coprime multiplication compatibility
- `ψ_surjective` (line 1026) — Shimura Thm 3.34 (generation of level-N algebra)
- **Thm 3.35 itself is PROVED** — it calls the sub-lemmas via `Ideal.Quotient.lift`
  - Blocked by: Props 3.32-3.33 (explicit coset decomposition for non-coprime det)
  - Key insight: the map MUST be a ring hom, not just additive — individual
    Gamma0 cosets with gcd(det,N)>1 arise from PRODUCTS, not individual GL cosets
  - The map: T(p)↦T'(p), T(p,p)↦T'(p,p) for p∤N, T(p,p)↦0 for p|N
  - Extends freely because R(Γ,Δ) is a polynomial ring (Thm 3.20)

### Key architectural decisions
- Used `Quotient` (dcSetoid) for HeckeCoset throughout
- `Delta0_submonoid` defined with explicit membership: int entries, det>0, N|c, gcd(a,N)=1
- `cosetMap` goes Gamma0→GL_pair (the "enlargement" direction)
- The reverse map (3.35 surjection) goes GL_pair→Gamma0 (needs ring structure)
- Strong approximation proved via Euclidean descent on coprime lifting, NOT via normal closures

### Next steps for Thm 3.35
1. Prove Prop 3.33: Γ'αΓ' = ∪ Γ'[1,r;0,m] for m|N^∞ (explicit upper-tri reps)
2. Prove Prop 3.32: Γ'αΓ' = (Γ'ξΓ')·(Γ'ηΓ') factorization
3. Prove Thm 3.34: R(Γ',Δ') is polynomial ring in listed generators
4. Define ring hom using polynomial ring universal property
