---
name: Hecke cleanup TODOs
description: Outstanding cleanup items for HeckeRIngs identified during overview
type: project
---

Outstanding cleanup items from the 2026-03-23 overview:

**1. maxHeartbeats decompositions** (7 proofs)
- `heckeSlash_fiber_sum` (6.4M, 161 lines) — worst offender
- `slash_tRep_product_eq` (3.2M, 62 lines) — extract K-correction helper
- `slash_tRep_of_mem` (3.2M, 39 lines) — similar to above
- `heckeSlash_slash_invariant` (1.6M, 64 lines)
- `left_coset_disjoint` (800K, 28 lines)
- `heckeSlash_bdd_at_cusps` (800K, 10 lines)
- `thm324_6` (400K, 11 lines)

**Why:** maxHeartbeats overrides are code smells — proofs should decompose into helpers that each compile within default budget.

**How to apply:** Use `/decompose-proof` on each. Extract shared patterns like "K-correction" and "same left coset → same slash" as reusable API.

**2. Deduplicate `intMat_det_cast`**
- Appears in: GLn/Basic.lean (private), GLn/CosetDecomposition.lean (private), GLn/DiagonalCosets.lean (private)
- Fix: Make it public in Basic.lean, remove the copies

**3. Remove deprecated aliases**
- `diagMul_pos` → alias for `pi_mul_pos` (CoprimeMul.lean:587)
- `T_ad'` → alias for `T_ad` (GL2/Basic.lean:84)

**4. Extract missing reusable API**
- `slash_eq_of_left_coset_eq`: "if two GL elements are in the same left H-coset, slashing by them gives the same result for Γ-invariant f" — pattern in `h_perm`, `slash_tRep_product_eq`, `slash_tRep_of_mem`
- `IsBoundedAt.sum`: finite sum of bounded-at-cusp functions is bounded

**5. Remaining sorries** (Shimura Thm 3.20)
- `T_gen_generates_R_p` in PolynomialRing.lean
- `R_p_isPolynomialRing` in PolynomialRing.lean
