# Hecke Theory — Ticket Tracker

> **Workers:** Check this file before starting work. Claim a ticket by writing your name in the
> Assignee column and changing status to `In Progress`. Push the update before you start coding.
> When done, set status to `Done` and list completed items in the Notes column.

## Quick Reference

**Plan:** `docs/plans/2026-03-10-hecke-theory-shimura-3-24.md`

**Rules:**
1. Only work on tickets with status `Available`
2. **Before starting:** Re-read this file to check the ticket is still `Available` (another worker may have claimed it). Set status → `In Progress`, set your name in Assignee, and push the update **before writing any code**
3. **During work:** After each significant milestone (e.g., key lemma proved, section completed), update the Notes column with a brief summary of progress and push
4. **When done:** Set status → `Done`, summarize what was proved in Notes, push. Then check if any `Blocked` tickets should be updated to `Available` (their dependencies may now be satisfied)
5. **If blocked:** Set status → `Blocked`, explain the blocker in Notes, push
6. Never edit files belonging to another in-progress ticket
7. **Code quality:** Before marking done, run `/simplify` on your code to remove verbose comments, ensure naming follows mathlib conventions (`camelCase` for defs/lemmas, no unnecessary abbreviations), and clean up any dead code. Run `lake build` to confirm everything compiles sorry-free

---

## Ticket Board

| # | Ticket | Status | Assignee | Files | Notes |
|---|--------|--------|----------|-------|-------|
| 1 | Degree Map | Done | Claude | `AbstractHeckeRing/Degree.lean` | `deg : 𝕋 P ℤ →+* ℤ`, sorry-free |
| 2 | Anti-Involution Commutativity | Done | Claude | `AbstractHeckeRing/Commutativity.lean` | All sorry-free. `m'_comm_of_onT'_eq` (Shimura Prop 3.8), `mul_comm_of_antiInvolution`, `instCommRing_of_antiInvolution`. Injection-based cardinality proof via `m'_le_comm`. |
| 3 | GL_n ArithmeticGroupPair | Done | Claude | `GLn/Basic.lean` | `GL_pair n`, all proofs sorry-free |
| 4 | Diagonal Representatives | Done | Claude | `GLn/DiagonalCosets.lean` | All sorry-free. 8 key theorems: `exists_diagonal_of_posdet`, `exists_divchain_of_posdiag`, `exists_divchain_diagonal_of_posdet`, `double_coset_eq_of_SLnZ_equiv`, `exists_diagonal_representative`, `diagonal_representative_unique`, `T_diag_span`, `partialProd_eq_of_SLnZ_equiv`. |
| 5 | Commutativity via Transpose | Available | - | `GLn/Commutativity.lean` | `CommRing (HeckeAlgebra n)` |
| 6 | Coset Decomposition & Degree | Done | Claude | `GLn/CosetDecomposition.lean`, `GLn/Degree.lean`, `GLn/CongruenceIndex.lean` | All sorry-free. Key theorems: `upperTriRep_card_le_T'_deg` (injection + S2 d=e via inverse-transpose + S1 δ-opacity), `T'_deg_T_diag_two_prime`, `T'_deg_T_diag_two_scalar`, `gaussianBinom`, `relIndex_conj_inv_eq_conj_diag`. |
| 7 | Coprime Product | Done | Claude | `GLn/CoprimeMul.lean` | All sorry-free. `T_diag_mul_coprime` (Shimura Prop 3.16), `T_diag_scalar_mul` (Prop 3.17). SLnZ transvec gen, CRT decomposition, Bezout coupling. |
| 8 | Prime Decomposition & Polynomial Ring | Done | Claude | `GLn/PrimeDecomposition.lean`, `GLn/PolynomialRing.lean` | `PrimeDecomposition.lean` sorry-free: `ppowDiag`, `pComponent`, `removePrime`, `T_elem_split_prime`, `T_elem_mem_closure_ppow`, `HeckeAlgebra_generated_by_R_p`, `R_p` subring. `PolynomialRing.lean`: `T_gen`, `T_gen_mem_R_p` sorry-free; `evalHom`/`R_p_isPolynomialRing` blocked on Ticket 5 (CommRing). |
| 9 | Theorem 3.24 (n=2) | In Progress | Claude | `GL2/Basic.lean`, `GL2/MultiplicationTable.lean` | 7 multiplication identities |
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

**Available now (no dependencies):** Tickets 5, 9

**Unblocks the most downstream work:** Ticket 5 (CommRing clears PolynomialRing sorries), Ticket 9 (gates 10)

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
| 2026-03-10 | 1 | Claude | `deg : 𝕋 P ℤ →+* ℤ` sorry-free: T'_deg, coeffSum, smulOrbit_card, deg_fun_mul (via IsScalarTower), full API |
| 2026-03-10 | 3 | Claude | `GL_pair n` sorry-free: SLnZ embedding, posDetInt submonoid, commensurator proof (Shimura Lemma 3.10 via congruence subgroups), API |
| 2026-03-11 | 4 | Claude | Diagonal representatives sorry-free: SNF existence via transvections, divisibility chains, Cauchy-Binet expansion for partial product invariance, uniqueness of diagonal representatives. Unblocks Ticket 6. |
| 2026-03-11 | 6 | Claude | Coset decomposition & degree sorry-free: upper-triangular injection into cosets, S2 (d=e) via inverse-transpose automorphism on SL_n(ℤ), S1 δ-opacity via `relIndex_pointwise_smul`, Γ₀(pᵏ) index formula, n=2 prime-power degree formula. Unblocks Ticket 7. |
| 2026-03-11 | 2 | Claude | Anti-involution commutativity sorry-free: `m'_comm_of_onT'_eq` (Shimura Prop 3.8) via injection-based cardinality (`m'_le_comm`), `mul_comm_of_antiInvolution`, `instCommRing_of_antiInvolution`. Unblocks Ticket 5. |
| 2026-03-12 | 7 | Claude | Coprime product sorry-free: `T_diag_mul_coprime` (Shimura Prop 3.16) via SLnZ transvec generation, CRT decomposition, Bezout coupling (`coprime_coupling_mem_H`). Also `T_diag_scalar_mul` (Prop 3.17). Unblocks Ticket 8. |
| 2026-03-12 | 8 | Claude | Prime decomposition & polynomial ring. `PrimeDecomposition.lean` sorry-free: p-adic decomposition (`ppowDiag`, `pComponent`, `removePrime`), binary splitting (`T_elem_split_prime`), full factorization (`T_elem_mem_closure_ppow`), generation (`HeckeAlgebra_generated_by_R_p`), `R_p` subring. `PolynomialRing.lean`: T_gen generators sorry-free (`T_gen_mem_R_p`); `evalHom`/`R_p_isPolynomialRing` blocked on Ticket 5. Unblocks Ticket 9. |

---

## Notes for Workers

### File & Build
- All new files go under `LeanModularForms/HeckeRIngs/`
- The existing abstract ring (`AbstractHeckeRing/`) is sorry-free — do not break it
- Run `lake build` before marking done — zero sorries, zero errors
- See the full plan for detailed code templates and proof strategies

### Checkout Protocol
1. **Read `docs/HECKE_TICKETS.md`** at the start of every session — do not rely on stale context
2. **Re-read before claiming** — another worker may have taken the ticket since you last checked
3. **Claim immediately** — update Status → `In Progress`, Assignee → your name, push. Do this before writing any code
4. **Push progress updates** — after proving key lemmas or completing sections, update the Notes column and push so other workers can see what's done
5. **Never start coding without claiming** — if two workers start the same ticket, one will have wasted effort

### Code Quality (before marking Done)
- Run `/simplify` on all new/modified files to clean up verbose comments and improve code quality
- Follow mathlib naming conventions: `camelCase` for defs and lemmas, descriptive names, no unnecessary abbreviations
- Remove long explanatory comments — the code and docstrings should be self-explanatory
- Keep module docstrings (`/-! ... -/`) concise: state what's defined/proved, cite Shimura reference
- Run `lake build` one final time to confirm sorry-free compilation
