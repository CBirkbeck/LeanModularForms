# Master Ticket Board: LeanModularForms → Strong Multiplicity One

*Consolidated 2026-04-17 from `tickets.md` (Bridge+Commutativity Refactor),
`tickets-prop-3-34.md` (Shimura Prop 3.34), and `tickets-finish-congruence-hecke.md`
(CongruenceHecke+BlockBijection).*

*Epic D (Adjoint Theory) remains in `tickets-phase5.md` as the authoritative
source; the Epic D summary below is a digest — refer to `tickets-phase5.md`
for complete up-to-date status from the active worker.*

## Overview

The final mathematical goal is **Strong Multiplicity One (Miyake Thm 4.6.12)**:
if f ∈ S_k^0(N, χ) and g ∈ S_k^1(N, χ) are common T(n)-eigenfunctions with the
same eigenvalue for all n coprime to some L, then g is a constant multiple of f.

This is pursued via 5 epics in approximately this order:

- **Epic A** (COMPLETE): Finish CongruenceHecke + BlockBijection (Shimura 3.20, 3.24, 3.35 n=2)
- **Epic B** (COMPLETE): Bridge + Commutativity Refactor (heckeRingHom chain)
- **Epic C** (MOSTLY DONE): Shimura Prop 3.34 (Gamma0MapUnits preservation)
- **Epic D** (ACTIVE, other worker): Hecke Adjoint Theory (Phase 5)
- **Epic E** (OPEN): POST-refactor work → SMO (Phases 6-9)

See `docs/plans/strong-multiplicity-one.md` for the master 9-phase plan and
`docs/plans/plan-prop-3-34.md` for Prop 3.34 design.

## Current totals

| Status | Count | Notes |
|---|---|---|
| Done | 26 | Incl. 8 completed this session |
| Superseded/resolved | 6 | Replaced by cleaner refactor |
| Blocked | 5 | Structural or gated on other epics |
| Open | 15 | Path forward to SMO |

**Immediate priorities** (can start now):
1. **POST-3** (Phase 7 L-functions) — independent, unblocked
2. **T201** (Γ₁(N) fund-domain) — independent, under active work by other worker
3. **POST-6** (Phase 8 Miyake Main Lemma) — mostly independent but deep

**Blocked** (documented with diagnostic):
- POST-1 (general-χ ring hom) — Quot.out structural issue
- POST-2 (heckeT_p_all_comm_distinct refactor) — gated on POST-1
- POST-4 (Newforms.lean:1523) — gated on T206/T207 (Epic D)
- POST-5 (Newforms.lean:1654) — gated on POST-3

---

# Epic A: Finish CongruenceHecke + BlockBijection (✅ COMPLETE)

*Originally in `tickets-finish-congruence-hecke.md`. All items done 2026-04-16.*

Target: `CongruenceHecke.lean` + `BlockBijection.lean` + `PolynomialRing.lean`
sorry-free at the n=2 level.

### [H-01] Gamma0_T1p_mul_T1ppow_coprime (Shimura 3.24 eq 5 at Γ₀(N)) ✅ done
- **File**: CongruenceHecke.lean
- **Result**: 315 LOC, filled sorry-free via Γ → Γ₀(N) surjection + cosetMap bridge.

### [B-01, B-02] BlockBijection.lean:1389, 1418 (Shimura 3.19 ≤/≥) ⚠️ partial
- **Status**: refactored via `heckeMultiplicity_rep_eq_diagMat_delta` bridge.
  Net sorry count unchanged (2 → 2); cleaner target for future work.
- **See**: memory `project_blockbijection_bridge.md`.

### [K-01] monomial_eval_kronecker ✅ done
- **File**: PolynomialRing.lean (moved from CongruenceHecke.lean:5022)
- **Result**: Full Kronecker delta proof; Inj namespace migrated.

### [C-01 through C-03] CongruenceHecke.lean cleanup ✅ done
- **Result**: 0 errors, 0 sorries.

### [P-01] evalHom_injective_two ✅ done
- **File**: PolynomialRing.lean:459
- **Result**: Filled sorry-free via monomial_eval_kronecker.

### [P-02, P-03] PolynomialRing.lean general-n ⛔ blocked on T2-F
- **Description**: General-n surjectivity/injectivity, blocked by BlockBijection
  ≤ direction (B-01). Acceptable to defer since n=1,2 suffices for SMO.

### [V-01, V-02] Final build check + cleanup ⚠️ ongoing
- **Status**: `lake build` clean; cleanup/audit ongoing as part of other phases.

---

# Epic B: Bridge + Commutativity Refactor (✅ COMPLETE)

*Originally `tickets.md` R001-R009, T020-T026. All done this session (2026-04-17)
via Γ₀(N) route — the original Γ₁(N) abstract-bridge path was structurally blocked
(adj-mismatch of D(1,p)/D(p,1) at Γ₁(N)).*

### [R001] Coset-independence for Hecke sums ✅ done
- **File**: GL2/HeckeActionGeneral.lean
- **Result**: `slash_tRep_gen_of_mem`, `heckeSlash_gen_slash_invariant`,
  `heckeSlash_gen_comp`, `heckeSlash_gen_comm` — all axiom-clean.

### [R002] `tRep_gen_D_p_matches_T_p_reps` + downstream ✅ done
- **File**: GL2/HeckeT_p_GLpair.lean (853L)
- **Result**: `heckeT_p_fun_eq_heckeSlash_gen`, `heckeT_p_fun_comm_of_GL_pair`, `heckeT_p_comm`.

### [R003] Bridge heckeT_n to heckeSlashExt_gen ✅ SUPERSEDED
- **Superseded by**: `heckeRingHom_Gamma0 N k` (HeckeModularForm_Gamma0.lean, 391L)
  and `heckeRingHomCharSpaceOne N k` (HeckeT_p_CharSpace_Comm.lean, 281L).
- **Note**: General-χ ring hom remains blocked (POST-1).

### [R004] Replace `heckeT_n_comm` proof with abstract version ⛔ BLOCKED
- **Blocker**: circular for general χ. Our session built
  `heckeT_p_all_charRestrict_commute_distinct` as a corollary OF the existing
  `heckeT_p_all_comm_distinct`. Breaking the cycle requires direct per-χ
  commutativity, blocked by POST-1.

### [R005] Verify build + cleanup (open)
- Status: build passes; cleanup ongoing.

### [R006] `heckeRingHom k : 𝕋 (GL_pair 2) ℤ →+* End(ModularForm 𝒮ℒ k)` ✅ done
- **File**: GL2/HeckeModularForm.lean (562L, +209 this session)
- **Upgraded**: from AddMonoidHom (original R006) to full RingHom.
- **Key decls**: `heckeSum`, `heckeRingHom`, `heckeRingHom_T_single`.

### [R007] Γ₁(N) Step 5 setup ✅ done
- **File**: GL2/HeckeT_p_Gamma1.lean (732L).
- **Key decls**: `D_p_Gamma1`, `sigma_p_specific`, `M_infty`, `slash_M_infty_eq_diamond_slash_T_p_lower`,
  `Gamma1_pair_H_entry_is_int`, `adj_upper_inv_mul_upper_not_mem_Gamma1`.

### [R008] Γ₁(N) bridge (cardinality + matching) ✅ SUPERSEDED (pivot to Γ₀(N))
- **Rationale**: at Γ₁(N), `adj(T_p_upper(b))` has top-left p ≢ 1 (mod N), so the
  adj factorization fails. Went via Γ₀(N) instead.
- **Achieved via pivot**: `D_p_Gamma0 N p hp`, `T_p_coset_reps_Gamma0_equiv`
  (Fin(p+1) ≃ decompQuot), `heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one`.

### [R009] R003+R004 vs R008 path ✅ RESOLVED
- Went with Γ₀(N) + character-decomposition route.

### [T020] Fin(p+1) ↪ decompQuot D_p_Gamma0 ✅ done (via Γ₀(N) pivot)
- **File**: GL2/HeckeT_p_Gamma0.lean (681L)
- **Key decl**: `T_p_coset_reps_Gamma0_equiv N p hp hpN : Fin (p+1) ≃ decompQuot …`.
- **Approach**: adj-based bijection works at Γ₀(N) since `adj(diag(1,p)) = T_p_lower ∈ D_p_Gamma0`.

### [T021] Conjugation preservation lemma ✅ done (generalized → Shimura Prop 3.34)
- **See Epic C** (P334-B below).

### [T022-T024] Γ₁(N) cardinality + bridge ✅ done (via Γ₀(N) pivot)
- **Achieved**: HeckeCoset_deg_D_p_Gamma0 = p+1, distinctness lemmas,
  `tRep_gen_D_p_Gamma0_matches_T_p_reps` (trivial-χ, with Γ₀(N)-invariant f).

### [T025] CommRing for 𝕋 (Gamma1_pair N) ℤ ⛔ BLOCKED
- **Blocker**: `onHeckeCoset D = D` fails at Γ₁(N) under any obvious anti-involution.
  Adj sends `D(1,p) ↦ D(p,1)` which is a DIFFERENT Γ₁(N)-double coset for p ≢ 1 (mod N).
  Atkin-Lehner `g ↦ wN·gᵀ·wN⁻¹` doesn't preserve Δ₁(N) integrality.
- **Workaround**: Use `CommRing (𝕋 (Gamma0_pair N) ℤ)` (exists) + char decomp.

### [T026] Final commutativity payoff ⛔ blocked on T025/POST-1

### [CLEANUP-2, CLEANUP-3] Cleanup tickets (open)

---

# Epic C: Shimura Prop 3.34 (✅ MOSTLY DONE)

*Originally `tickets-prop-3-34.md`. P334-A through D done. P334-E/F/G partially
done; remaining blockers documented under POST-1.*

### [P334-A] Precise statement + matrix entry lemma ✅ done
- **File**: GL2/Prop334.lean (189L → 373L)
- **Key decls**: `matrix_fin_two_conj_entry_11_mod_eq` + `_00_mod_eq`,
  `N_dvd_adj_mul_mul_entry_11_sub` + `_00_sub`.

### [P334-B] Good-prime case of Prop 3.34 ✅ done
- **File**: GL2/Prop334.lean (+184L)
- **Key decl**: `Gamma0MapUnits_preserved_of_detCoprime` — `CoprimeDet`-form.

### [P334-C] Bad-prime case ❌ skipped (good-prime suffices)

### [P334-D] Assemble full Prop 3.34 ✅ done (via P334-B)

### [P334-E] heckeSlash_gen preservation of modFormCharSpace ⚠️ partial
- **File**: GL2/Prop334_HeckeSlash.lean (283L)
- **Delivered**: wrapping infrastructure + reduction given `hComm` hypothesis.
- **Blocker**: `hComm` itself (Quot.out dependence) — see POST-1.

### [P334-StabSurj] Stabilizer surjectivity (diagonal case) ✅ done
- **File**: GL2/Prop334_StabSurj.lean (298L)
- **Key decl**: `Gamma0MapUnits_surjOn_stab_diag` — for diag(1,k), stab surjects onto (ZMod N)ˣ.

### [P334-HeckeSlashDiag] χ-equivariance of heckeT_p_fun ✅ done
- **File**: GL2/Prop334_HeckeSlashDiag.lean (207L)
- **Key decls**: `heckeT_p_fun_slash_comm_charSpace`,
  `heckeSlash_gen_functional_equivariance_D_p_Gamma0_trivial` (trivial-χ target done),
  `heckeSlash_gen_functional_equivariance_D_p_Gamma0_of_bridge` (conditional general-χ).

### [P334-Path1] Explicit slash + χ-equivariance ✅ done (+diagnostic)
- **File**: GL2/HeckeSlashExplicit.lean (273L)
- **Delivered**: `heckeSlash_explicit_D_p_Gamma0` = heckeT_p_fun (definitional);
  χ-equivariance; `M_infty_mem_D_p_Gamma0`.
- **Documented finding**: `heckeSlash_gen D_p_Gamma0 f ≠ heckeT_p_fun f` for
  general χ (Quot.out arbitrary-choice noise).

### [P334-F] heckeRingHomCharSpace for arbitrary χ ⛔ BLOCKED → POST-1
### [P334-G] Refactor heckeT_p_all_comm_distinct via ring hom ⛔ BLOCKED → POST-2

---

# Epic D: Hecke Adjoint Theory (⚠️ ACTIVE — other worker)

*Authoritative source: `tickets-phase5.md` — this section is a digest.
Owned by another worker; do NOT modify `AdjointTheory.lean`/`DeltaEigenform.lean`/
`Newforms.lean`/`FourierHecke.lean` without coordination.*

**Active files**: GL2/AdjointTheory.lean (2643L, 2 sorries), Modularforms/PeterssonLevelN.lean,
PeterssonInner.lean, PSL2Action.lean.

### Done (7)

- **T100a** `diamondOp_petersson_unitary` ✅ — via `petN_slash_invariant`.
- **T100b** `heckeT_n_adjoint_on_charSpace` ✅ — via heckeT_n_adjoint + petN_smul_right.
- **T101** GL₂⁺(ℝ) invariance of μ_hyp ✅ — `instSMulInvMeasure_GLpos` (PSL2Action.lean:545).
- **T103** `peterssonInner_slash_adjoint` ✅ (Prop 5.5.2a) — AdjointTheory.lean:616-664.
- **T105** Double coset identity algebraic part ✅ — `adjointGamma0Rep`, `_units` proved.
- **T108** `heckeT_n_cusp_isSemisimple_on_charSpace` ✅ — one-liner via Mathlib.
- **T204** `petN_slash_adjoint_GL2` + `sum_setIntegral_GL2_shift` ✅ (2026-04-17).
- **T205-a** Per-summand slash adjoint for T_p coset reps ✅ (2026-04-18).
- **T206** heckeT_n_adjoint composite case ✅ (2026-04-13).

### Open — Foundation tickets

### [T201] `IsFundamentalDomain` for Γ₁(N) coset tiling
- **Status**: open (independent)
- **File**: PeterssonLevelN.lean
- **Description**: Prove `IsFundamentalDomain (imageGamma1 N) D_N μ_hyp` where
  `D_N := ⋃ q : SL(2,ℤ) ⧸ Gamma1 N, q.out⁻¹ • fdo`.
- **Estimated**: 80-100 LOC.

### [T202] Relate petN to integral over fundamental domain
- **Depends on**: T201.
- **File**: PeterssonLevelN.lean.
- **Statement**: `petN f g = ∫ τ in D_N, petersson k ⇑f ⇑g τ ∂μ_hyp`.
- **Estimated**: 40-60 LOC.

### [T203] Domain shift invariance for Γ₁(N)-normalizing elements
- **Depends on**: T201.
- **Statement**: `IsFundamentalDomain_Gamma1_shift` + `setIntegral_fundDomain_eq_of_Gamma1_invariant`.
- **Estimated**: 40-60 LOC.

### Open — Core Adjoint

### [T205 / T205-d] `petN_heckeT_p_diamond_shift_core` (sorry #2)
- **Status**: in progress (other worker, currently stuck on combinatorial bijection)
- **File**: AdjointTheory.lean (sorry near line 1586)
- **Done**: T205-a (per-summand slash adjoint), triple product identity,
  T_p_lower slash decomposition, all scaffolded.
- **Remaining**: σ-reindex on SL(2,ℤ) ⧸ Γ₁(N) absorbing γ₀ + matrix matching
  (b,q) ↔ (c,q'). ~80-150 LOC.
- **Key blocker**: `T_p_upper(0)` doesn't normalize Γ₁(N), so template from
  `petN_slash_invariant` doesn't directly apply.

### [T207] `exists_simultaneous_eigenform_basis` (sorry #4)
- **Depends on**: T206 (via heckeT_n_adjoint).
- **File**: AdjointTheory.lean:1270.
- **Statement**: orthogonal basis of common eigenforms for {T_n, ⟨n⟩ : (n,N)=1}.
- **Approach**: 3 steps — joint eigenspace decomp via Mathlib's
  `Module.End.iSup_iInf_maxGenEigenspace...`, basis extraction, orthogonality.
- **Estimated**: 80-120 LOC.

### [T208] Fix stale comments + cleanup
- **Type**: cleanup.
- Fix comments claiming `heckeT_n_comm` is sorry'd (lines 1266, 1284, 1323) — it's fully proved.
- Remove dead code (lines 668-692).
- Merge `petN_heckeT_p_adjoint_unsymm` with `heckeT_p_adjoint_of_diamond_shift`.

---

# Epic E: POST-refactor + SMO progression

*New tickets from the 2026-04-17 session + path to SMO.*

## Blocked tickets (structural or gated on other epics)

### [POST-1] General-χ ring hom `𝕋 (Gamma0_pair N) →+* End(modFormCharSpace k χ)` ⛔ BLOCKED
- **Status**: structurally blocked.
- **Blocker**: `heckeSlash_gen D f` uses `Classical.choice`-chosen `Quot.out` reps.
  For `f ∈ modFormCharSpace k χ` with χ ≠ 1, changing σ.out picks up χ-factors
  depending on arbitrary choices. The sum `Σ_σ f ∣ tRep_gen σ` doesn't equal
  `heckeT_p_fun f` in general.
- **Resolution paths** (pick one):
  - (a) Char-aware matching theorem using M_∞ instead of T_p_lower as p+1-th rep
  - (b) Redefine `heckeSlash_gen` for D_p_Gamma0 to use explicit reps (Shimura/DS style)
  - (c) Accept the current state — commutativity is already achieved at heckeT_p_all level
- **Estimated**: 400+ LOC if pursued via (a) or (b).

### [POST-2] Refactor `heckeT_p_all_comm_distinct` (HeckeT_n.lean:1071) ⛔ BLOCKED on POST-1
- **Description**: Replace 200-line manual proof with short one via char decomp
  + per-χ ring hom.
- **Cleanup impact**: would delete ~1000 LOC of helper lemmas (heckeT_p_all_comm_heckeT_ppow,
  heckeT_ppow_comm_same, heckeT_ppow_comm_heckeT_ppow, etc.).

### [POST-4] Newforms.lean:1523 sorry (new-subspace forcing zero) ⛔ BLOCKED on Epic D
- **File**: GL2/Newforms.lean:1523
- **Depends on**: `heckeT_n_adjoint`, `exists_simultaneous_eigenform_basis` (Epic D).
- **Description**: Once adjoint theory completes, closes as a short corollary.

### [POST-5] Newforms.lean:1654 sorry (exists_nonzero_prime_eigenvalue) ⛔ BLOCKED on POST-3
- **File**: GL2/Newforms.lean:1654
- **Depends on**: L-function theory.
- **Description**: Needs Euler product argument at bad primes to exclude vanishing.

## Open tickets (can proceed now)

### [POST-3] Phase 7: L-function infrastructure
- **Status**: open, HIGH PRIORITY (independent of POST-1, Epic D).
- **File**: new `GL2/LFunction.lean` or `Eigenforms/LFunction.lean`.
- **Depends on**: nothing (Phase 3 complete).
- **Description**: Define `L(s, f) = Σ a_n n^{-s}`; prove convergence for cusp forms;
  prove Euler product ⟺ normalized eigenform.
- **Reference**: [DS] §5.9, [Miy] Thm 4.5.16. See `docs/plans/strong-multiplicity-one.md` §Phase 7.
- **Estimated**: 500 LOC.

### [POST-6] Phase 8: Miyake Main Lemma (Thm 4.6.8)
- **Status**: open.
- **Depends on**: Phase 6 complete (POST-4, POST-5) or most of it.
- **File**: new `Eigenforms/MainLemma.lean`.
- **Description**: If `f ∈ G_k(N, χ)` and `a_n = 0` for all n prime to `l`:
  either `f = 0` or `f = Σ f_p(pz)` for `p | (l, N/m_χ)`.
- **Reference**: [Miy] Thm 4.6.8. See `docs/plans/strong-multiplicity-one.md` §Phase 8.
- **Estimated**: 1000 LOC.

### [POST-7] Phase 9: Strong Multiplicity One (Miyake Thm 4.6.12) — FINAL GOAL
- **Status**: open.
- **Depends on**: POST-4, POST-5, POST-6.
- **File**: new `Eigenforms/StrongMultiplicityOne.lean`.
- **Description**: Short ~400 LOC proof once Phases 6 and 8 are in place.
- **Reference**: See `docs/plans/strong-multiplicity-one.md` §Phase 9.

---

# Dependency graph

```
Epic A (CongruenceHecke/BlockBijection) ✅
   └──→ Epic B (Bridge + Commutativity) ✅
          └──→ Epic C (Shimura Prop 3.34) ⚠️
                 ├──→ POST-1 (general-χ ring hom) ⛔
                 │      └──→ POST-2 (comm_distinct refactor) ⛔
                 └──→ [stopping point — commutativity achieved]

Epic D (Adjoint Theory) ⚠️ ACTIVE
   ├──→ POST-4 (Newforms L1523) ⛔
   └──→ T207 (eigenform basis) → POST-6 (Miyake Main Lemma)
                                    └──→ POST-7 (SMO) ◄── FINAL GOAL
Phase 3 (T_n+Fourier) ✅
   └──→ POST-3 (L-functions) ◄── PARALLELIZABLE NOW
          └──→ POST-5 (Newforms L1654) ⛔
                 └──→ POST-6 → POST-7
```

**Critical path to SMO**: Epic D complete → POST-4 → POST-6 → POST-7.
**Parallel track**: POST-3 (independent).

---

# Session commits (2026-04-17)

- `a7b2391` — Hecke ring → End commutativity refactor (9 new files, 5500 LOC)
- `bf3dba1` — Prop 3.34 infrastructure + trivial-χ unblock (500 LOC)
- `bdd7738` — Path 1 explicit slash + diagnostic (273 LOC)
- `8bbe661` — docs/plans/SMO plan update
- `2ad4cd2` — tickets.md update (superseded by this consolidation)

Other worker's recent commits interleaved (AdjointTheory T205 scaffold, peterssonInner helpers).
