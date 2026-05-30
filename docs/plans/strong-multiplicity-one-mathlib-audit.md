# Mathlib Audit for Strong Multiplicity One Plan

Generated: 2026-03-28

## What Mathlib Gives Us Directly

### Modular Forms Core
- `ModularForm Γ k` — structure with holomorphicity, slash invariance, bounded at cusps
- `CuspForm Γ k` — vanishes at cusps
- `SlashInvariantForm Γ k` — slash invariance only
- `ModularFormClass`, `CuspFormClass` — typeclasses
- All have `AddCommGroup`, `Module ℂ`, `FunLike` instances

### Slash Action
- `SlashAction` typeclass with `f |[k] g` notation
- `SlashAction.slash_mul`: `(f |[k] g₁) |[k] g₂ = f |[k] (g₁ * g₂)`
- `SlashAction.add_slash`, `SlashAction.neg_slash` — linearity
- `SlashInvariantForm Γ k` is bundled for the ordinary slash action only; it is not
  parameterized by a custom action, so Nebentypus should be introduced via a local
  twisted-slash layer plus explicit bridge API rather than by trying to mutate the
  existing mathlib abstraction in this project

### Congruence Subgroups
- `CongruenceSubgroup.Gamma N` — principal congruence subgroup
- `CongruenceSubgroup.Gamma0 N` — upper triangular mod N
- `CongruenceSubgroup.Gamma1 N` — upper triangular, diagonal ≡ 1 mod N
- `IsCongruenceSubgroup` predicate
- `FiniteIndex` instances for all three
- `Gamma1_in_Gamma0` — inclusion

### q-Expansion
- `ModularFormClass.qExpansion` — as `PowerSeries ℂ`
- `ModularFormClass.hasSum_qExpansion` — convergence
- `qExpansion_coeff_unique` — coefficients determine the form
- `CuspFormClass.cuspFunction_apply_zero` — a₀ = 0 for cusp forms

### Dirichlet Characters
- `DirichletCharacter R n` — type (group hom `(ZMod n)ˣ → Rˣ`)
- `DirichletCharacter.conductor` — minimal level
- `DirichletCharacter.IsPrimitive` — conductor = level
- `DirichletCharacter.primitiveCharacter` — associated primitive character
- `DirichletCharacter.FactorsThrough` — factors through lower level

### L-functions Infrastructure
- `LSeries` — general L-series `Σ a(n)/n^s`
- `DirichletCharacter.LFunction` — meromorphic continuation
- `DirichletCharacter.LSeries_eulerProduct` — Euler product for Dirichlet L-functions
- Hurwitz zeta, Riemann zeta, functional equations all present

### Upper Half Plane
- `UpperHalfPlane` — `{z : ℂ // 0 < z.im}`
- `UpperHalfPlane.SLAction` — SL₂(ℝ) action
- `UpperHalfPlane.instMetricSpace` — Poincaré metric
- `ModularGroup.fdo` / `ModularGroup.fd` — fundamental domain as a set
- `ModularGroup.exists_smul_mem_fd` — reduction into the standard fundamental domain
- `ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo` — uniqueness on the open fundamental domain
- `UpperHalfPlane.norm_qParam_lt_one` — |q(τ)| < 1

### SL₂(ℤ) / Matrix Groups
- `Matrix.SpecialLinearGroup` with `Group` instance
- `ModularGroup.T`, `ModularGroup.S` — generators
- `SpecialLinearGroup.SL2Z_generators` — T, S generate SL₂(ℤ)
- `Subgroup.HasDetOne`, `Subgroup.HasDetPlusMinusOne` — typeclasses

### Spectral Theory (KEY for eigenform diagonalization)
- `Module.End.eigenspace f μ = ker(f - μ)` — eigenspaces
- `Module.End.eigenspaces_independent` — eigenspaces are linearly independent
- `LinearMap.IsSymmetric.direct_sum_isInternal` — symmetric operator = direct sum of eigenspaces
- **`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`** — FAMILY of pairwise commuting
  symmetric operators: **simultaneous diagonalization** on finite-dim inner product space
- `LinearMap.IsSymmetric.directSum_isInternal_of_commute` — two commuting symmetric ops

### Eisenstein Series
- Full Eisenstein series for k ≥ 3, level Γ(N)
- Summability, uniform convergence, MDifferentiable
- q-expansion, boundedness at infinity

### Fundamental Domain Theory
- `MeasureTheory.IsFundamentalDomain` — predicate
- `QuotientMeasureEqMeasurePreimage` — quotient measure theory
- `IsFundamentalDomain.measurePreserving_quotient_mk`

### Dimension Formulas
- `ModularForm.levelOne_weight_zero_rank_one` — dim M₀(SL₂(ℤ)) = 1
- `ModularForm.levelOne_neg_weight_rank_zero` — dim M_k = 0 for k < 0

---

## What Is Partially Available

### Petersson Inner Product
- **Have**: Integrand `petersson k f g τ = conj(f τ) * g τ * τ.im^k`
- **Have**: SL₂ invariance `petersson_slash_SL`
- **Have**: Exponential decay `petersson_exp_decay_left/right`
- **Missing**: Hyperbolic measure dxdy/y², integral, convergence, inner product space structure

### Fundamental Domain (measure-theory)
- **Have**: `ModularGroup.fd` / `ModularGroup.fdo` for the standard domain
- **Have**: `ModularGroup.exists_smul_mem_fd` for the reduction algorithm
- **Have**: `ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo` for uniqueness on the open domain
- **Missing**: A packaged bridge from this existing API to the exact
  `MeasureTheory.IsFundamentalDomain` / quotient-integration interface needed for Petersson theory

### Hecke Operators (our project)
- **Have**: `heckeOperator`, `heckeOperatorLinear`, `heckeOperator_comp` for SL₂(ℤ)
- **Missing**: Level-N versions (Γ₁(N) Hecke pair)

### Character / Nebentypus Layer
- **Have**: ordinary slash-invariant bundled forms and the congruence-subgroup API
- **Missing**: a local `Γ₀(N)` character-twisted slash action and bridges showing:
  trivial character = ordinary `Γ₀(N)` modular forms, and twisted-slash invariance =
  the existing `Γ₁(N)` diamond-eigenspace view

### Trace/Norm Maps
- **Have**: `NormTrace.lean` in mathlib
- **Missing**: Connection to Hecke theory

---

## What Is Completely Missing

| Component | Phase | Difficulty |
|-----------|-------|------------|
| Hyperbolic measure dxdy/y² on ℍ | 4 | Hard |
| Petersson inner product (integral + convergence) | 4 | Hard |
| InnerProductSpace on CuspForm Γ k | 4 | Hard |
| Hecke pair for Γ₁(N) (Δ₁(N) submonoid) | 1 | Medium |
| Diamond operator ⟨d⟩ on M_k(Γ₁(N)) | 2 | Medium |
| T_p specialized to Γ₁(N) | 2 | Medium |
| Character eigenspace decomposition M_k(Γ₁(N)) = ⊕ M_k(N,χ) | 2 | Medium |
| T_n for general n (recurrence + multiplicativity) | 3 | Medium |
| Fourier coefficient formula a_n(T_p f) = a_{np} + χ(p)p^{k-1}a_{n/p} | 3 | Medium |
| Eigenvalue = Fourier coefficient (Miyake 4.5.16) | 3 | Medium |
| Self-adjointness T_n* = ⟨n⟩⁻¹T_n | 5 | Medium |
| Eigenform / IsHeckeEigenform predicate | 5 | Easy |
| Eigenform basis (via spectral theorem) | 5 | Medium |
| Level embedding f(z) ↦ f(lz) | 6 | Easy |
| S_k^0 / S_k^1 decomposition (primitive/lower-level) | 6 | Medium |
| Primitive form definition and properties | 6 | Medium |
| Hecke's Lemma (Miyake 4.6.3) | 6 | Medium |
| Conductor theorem (Miyake 4.6.4) | 6 | Hard |
| Coprime sieve (Miyake 4.6.5) | 6 | Medium |
| Main Lemma decomposition (Miyake 4.6.8) | 8 | Hard |
| L(s,f) for modular forms | 7 | Medium |
| Euler product ↔ normalized eigenform | 7 | Medium |
| Strong Multiplicity One (Miyake 4.6.12) | 9 | Medium |
| General dimension formula dim M_k(Γ) | — | Hard (not blocking) |

---

## Critical Path Analysis

### Bottleneck: Petersson Inner Product (Phase 4)

Everything after Phase 4 depends on having the inner product:
- Phase 5 (adjoints) needs ⟨T_p f, g⟩ = ⟨f, T_p* g⟩
- Phase 6 (primitive forms) needs S_k^0 = (S_k^1)⊥
- Phase 9 (SMO) needs orthogonal decomposition

The Petersson inner product requires:
1. Hyperbolic measure dxdy/y² (not in mathlib)
2. Reusing the existing modular-domain reduction/uniqueness API and packaging it into the
   measure-theoretic interface needed for integration; this is narrower than formalizing the
   standard domain from scratch
3. Convergence of the integral (via cusp form decay, partially in mathlib)

### Parallel Work Possible

```
Phases 1-3 (Hecke pair + T_n + Fourier)  ←→  Phase 4 (Petersson)
                                                    ↓
                                              Phase 5 (adjoints)
                                                    ↓
Phase 7 (L-functions) ←─── Phase 3 ──→  Phase 6 (primitive forms)
                                                    ↓
                                              Phase 8 (Main Lemma)
                                                    ↓
                                              Phase 9 (SMO)
```

### Key Mathlib Theorem to Exploit

**`LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`**: Once we have:
- Inner product on S_k(Γ₁(N)) (Phase 4)
- T_n is symmetric (self-adjoint) w.r.t. this inner product (Phase 5)
- T_n's pairwise commute (Phase 2-3)

Then this single mathlib theorem gives us the eigenform basis for free — no need to
build our own spectral theory.
