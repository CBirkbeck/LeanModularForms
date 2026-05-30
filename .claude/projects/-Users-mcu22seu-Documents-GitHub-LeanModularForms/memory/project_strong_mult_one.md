---
name: Strong Multiplicity One Plan
description: Comprehensive plan for proving the strong multiplicity one theorem for modular forms, with 7 phases from diamond operators to the final theorem
type: project
---

Plan written to `docs/plans/strong-multiplicity-one.md` on 2026-03-27.

**Goal**: Prove Strong Multiplicity One (Miyake Thm 4.6.12 / Diamond-Shurman Thm 5.8.2).

**7 Phases**:
1. Diamond operators ⟨d⟩ and T_p on Γ₁(N) — connect abstract Hecke ring to congruence subgroups
2. T_n operators and Fourier coefficient formula — eigenvalue = Fourier coefficient
3. Petersson inner product on S_k(Γ₁(N)) — inner product space structure
4. Adjoint theory + eigenform basis — T_n normal → spectral theorem
5. Oldform/newform decomposition — S_k = S_k^old ⊕ S_k^new
6. Main Lemma (Atkin-Lehner) — a_n=0 for (n,N)=1 → f is old
7. Strong Multiplicity One — newforms determined by eigenvalues

**Key design decisions**:
- New `HeckePair` for Γ₁(N) (not just SL₂(ℤ)) to reuse abstract theory
- Eigenform as predicate `IsHeckeEigenform` + bundled `HeckeEigenform` structure
- Newform = normalized eigenform in S_k^new (orthogonal complement of oldforms)
- Petersson inner product may be axiomatized initially

**References**: Diamond-Shurman Ch.5, Miyake §4.5-4.6, Shimura Ch.3
