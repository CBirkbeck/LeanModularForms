# Hecke Theory — Ticket Tracker

> **Workers:** Check this file before starting work. Claim a ticket by writing your name in the
> Assignee column and changing status to `In Progress`. Push the update before you start coding.
> When done, set status to `Done` and list completed items in the Notes column.

## Quick Reference

**Plan:** `docs/plans/2026-03-10-hecke-theory-shimura-3-24.md`

**Rules:**
1. Only work on tickets with status `Available`
2. Before starting: set status → `In Progress`, set your name, push
3. When done: set status → `Done`, summarize what was proved, push
4. If blocked: set status → `Blocked`, explain in Notes
5. Never edit files belonging to another in-progress ticket

---

## Ticket Board

| # | Ticket | Status | Assignee | Files | Notes |
|---|--------|--------|----------|-------|-------|
| 1 | Degree Map | Available | - | `AbstractHeckeRing/Degree.lean` | `deg : 𝕋 P ℤ →+* ℤ` |
| 2 | Anti-Involution Commutativity | Available | - | `AbstractHeckeRing/Commutativity.lean` | `CommRing` criterion via anti-involution |
| 3 | GL_n ArithmeticGroupPair | Available | - | `GLn/Basic.lean` | `GL_pair n`, embeddings, commensurator proof |
| 4 | Diagonal Representatives | Blocked (needs 3) | - | `GLn/DiagonalCosets.lean` | Smith normal form, `T(a₁,...,aₙ)` |
| 5 | Commutativity via Transpose | Blocked (needs 2,3) | - | `GLn/Commutativity.lean` | `CommRing (HeckeAlgebra n)` |
| 6 | Coset Decomposition & Degree | Blocked (needs 4) | - | `GLn/CosetDecomposition.lean`, `GLn/Degree.lean` | Upper-triangular reps, Gaussian binomials |
| 7 | Coprime Product | Blocked (needs 4,6) | - | `GLn/CoprimeMul.lean` | `T(a)·T(b)=T(ab)` when coprime |
| 8 | Prime Decomposition & Polynomial Ring | Blocked (needs 7) | - | `GLn/PrimeDecomposition.lean`, `GLn/PolynomialRing.lean` | R_p^(n) ≅ ℤ[T₁,...,Tₙ] |
| 9 | Theorem 3.24 (n=2) | Blocked (needs 8) | - | `GL2/Basic.lean`, `GL2/MultiplicationTable.lean` | 7 multiplication identities |
| 10 | Hecke Operators | Blocked (needs 9,1) | - | `GL2/HeckeOperator.lean` | Action on modular forms |

---

## Dependency Graph

```
 1 (Degree)  ─────────────────────────────────────────────┐
                                                          ▼
 2 (AntiInv) ──────────┐                              10 (HeckeOps)
                        ▼                                 ▲
 3 (GL_n) ──┬──► 5 (Commutativity)                       │
            │                                             │
            └──► 4 (Diagonal) ──► 6 (Cosets) ──► 7 (Coprime) ──► 8 (Polynomial) ──► 9 (Thm 3.24)
```

**Available now (no dependencies):** Tickets 1, 2, 3

**Unblocks the most downstream work:** Ticket 3 (gates 4→6→7→8→9→10)

---

## Status Legend

| Status | Meaning |
|--------|---------|
| `Available` | Ready to work on — all dependencies met |
| `In Progress` | Someone is actively working on it |
| `Blocked (needs X)` | Dependencies not yet complete |
| `Done` | Complete and sorry-free |

---

## Completed Work Log

_Record completed tickets here with date and summary._

| Date | Ticket | Worker | Summary |
|------|--------|--------|---------|
| - | - | - | - |

---

## Notes for Workers

- All new files go under `LeanModularForms/HeckeRIngs/`
- The existing abstract ring (`AbstractHeckeRing/`) is sorry-free — do not break it
- Run `lake build` before marking done
- See the full plan for detailed code templates and proof strategies
- When a ticket is completed, check if any blocked tickets should be updated to `Available`
