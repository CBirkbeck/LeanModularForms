# Project Overview: SMOObligations dependency closure — cleanup audit

Generated: 2026-05-22
Scope: the transitive import closure of `LeanModularForms/SMOObligations.lean` — **95 modules, 108,835 lines** (HeckeRIngs/{GL2,GLn,AbstractHeckeRing}, Eigenforms, and the Modularforms files in that closure).
Emphasis (per request): surface comment bloat, over-long proofs, oversized files, and decompose/split candidates to drive a follow-up `/cleanup-all` pass.

## Executive Summary

The SMO closure carries large, uniform cleanup debt — the user's read ("almost all of these files need cleaning") is confirmed by the metrics. Across 95 files: **517 proofs exceed 50 lines, 128 exceed 100 lines, 21 files exceed 1,000 lines, and there are 1,754 standalone `--` comment lines plus very large block-comment volumes** (Newforms alone has ~6,500 block-comment lines, BlockBijection ~1,950). The debt is concentrated in five files — `Newforms.lean` (19,131 L), `AdjointTheory.lean` (17,704 L), `BlockBijection.lean` (9,398 L), `SMOObligations.lean` (6,462 L), `CongruenceHecke.lean` (5,814 L) — which together hold the bulk of the over-long proofs.

The top priority is **structural**, not golf: the five megafiles should be `/split-file`'d, and the 128 proofs >100 lines (and the 517 >50) should be `/decompose-proof`'d, *before* (or interleaved with) per-file `/cleanup` golf — otherwise `/cleanup` workers choke on 19K-line files and 300-line proofs (as observed: `/cleanup-all` mega-file workers could only do conservative comment/style passes on them).

The mathematics is in good shape: the Hecke-operator theory was just unified through the ring-hom `heckeRingHomCharSpace` (the two parallel "islands" are now bridged), SMO is axiom-clean, and the q-expansion ↔ operator API already exists. So this audit is about *form* (size, comments, proof length), not correctness or missing math.

## Statistics

- Files: 95 · Lines: 108,835
- Proofs >30 lines: **1,049** · >50 lines: **517** · >100 lines: **128** (span-proxy: gap between consecutive declaration starts)
- Standalone `--` comment lines: **1,754**
- Files >1,000 lines: **21** · Files >5,000 lines: **5**
- Pre-existing sorries in closure: Newforms (2), BlockBijection (1), Projection (4), PolynomialRing (2, general-n only) — all outside SMO's *proof* dependency (SMO is axiom-clean).

---

## Part 1: Per-file cleanup metrics (priority-sorted)

Columns: `lines` · `--cmt` (standalone comment lines) · `blkC` (lines inside `/- … -/` blocks) · `decl` (declarations) · `>30`/`>50`/`>100` (proofs over that many lines, span proxy) · `maxSpan` (longest declaration span). Files with no cleanup signal (small, no long proofs, no comment bloat) are omitted — they're fine as-is.

| file | lines | --cmt | blkC | decl | >30 | >50 | >100 | maxSpan |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| HeckeRIngs/GL2/Newforms.lean | 19131 | 651 | 6505 | 533 | 213 | 111 | 26 | 311 |
| HeckeRIngs/GL2/AdjointTheory.lean | 17704 | 23 | 512 | 537 | 203 | 119 | 20 | 261 |
| HeckeRIngs/GLn/BlockBijection.lean | 9398 | 0 | 1950 | 237 | 99 | 58 | 16 | 325 |
| SMOObligations.lean | 6462 | 4 | 397 | 170 | 61 | 41 | 10 | 517 |
| HeckeRIngs/GLn/CongruenceHecke.lean | 5814 | 59 | 508 | 139 | 50 | 31 | 15 | 330 |
| Eigenforms/MainLemma.lean | 2631 | 0 | 485 | 90 | 37 | 13 | 1 | 114 |
| HeckeRIngs/GL2/HeckeT_n.lean | 2055 | 0 | 127 | 69 | 18 | 11 | 5 | 192 |
| HeckeRIngs/GL2/HeckeT_p.lean | 1264 | 80 | 144 | 35 | 10 | 9 | 3 | 140 |
| Modularforms/LFunction.lean | 1919 | 0 | 777 | 74 | 22 | 5 | 0 | 68 |
| HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean | 1865 | 104 | 379 | 81 | 15 | 5 | 2 | 164 |
| Modularforms/summable_lems.lean | 1511 | 0 | 8 | 86 | 16 | 4 | 0 | 54 |
| HeckeRIngs/GL2/FourierHecke.lean | 1077 | 0 | 116 | 23 | 9 | 6 | 5 | 155 |
| HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean | 1331 | 0 | 99 | 69 | 9 | 6 | 2 | 109 |
| HeckeRIngs/GLn/PolynomialRing.lean | 1225 | 82 | 133 | 51 | 8 | 5 | 3 | 185 |
| HeckeRIngs/AbstractHeckeRing/Associativity.lean | 730 | 7 | 18 | 18 | 7 | 7 | 1 | 117 |
| Modularforms/PeterssonLevelN.lean | 1763 | 3 | 661 | 93 | 17 | 3 | 0 | 78 |
| HeckeRIngs/GLn/DiagonalCosets.lean | 1086 | 0 | 57 | 61 | 10 | 5 | 1 | 110 |
| Modularforms/Eisenstein.lean | 1054 | 13 | 48 | 71 | 10 | 5 | 0 | 74 |
| HeckeRIngs/GL2/MultiplicationTable.lean | 1183 | 6 | 75 | 53 | 13 | 3 | 1 | 108 |
| Eigenforms/AtkinLehner.lean | 1892 | 0 | 757 | 80 | 14 | 2 | 1 | 131 |
| Eigenforms/ConductorTheorem.lean | 1971 | 0 | 683 | 88 | 11 | 3 | 1 | 136 |
| Modularforms/PSL2Action.lean | 1014 | 103 | 218 | 53 | 10 | 3 | 0 | 77 |
| HeckeRIngs/GL2/LevelRaise.lean | 977 | 37 | 331 | 41 | 10 | 3 | 1 | 113 |
| Modularforms/QExpansionSlash.lean | 960 | 99 | 167 | 9 | 6 | 3 | 3 | 362 |
| HeckeRIngs/GL2/HeckeT_p_GLpair.lean | 817 | 108 | 129 | 28 | 8 | 2 | 1 | 176 |
| HeckeRIngs/GL2/HeckeT_p_Gamma1.lean | 732 | 25 | 252 | 31 | 7 | 5 | 1 | 110 |
| HeckeRIngs/GLn/CoprimeMul.lean | 876 | 0 | 32 | 43 | 9 | 2 | 0 | 88 |
| HeckeRIngs/GL2/CharacterDecomp.lean | 858 | 23 | 235 | 48 | 7 | 3 | 0 | 74 |
| HeckeRIngs/GL2/HeckeActionGeneral.lean | 788 | 1 | 129 | 49 | 7 | 2 | 0 | 91 |
| HeckeRIngs/AbstractHeckeRing/Multiplication.lean | 798 | 15 | 110 | 46 | 7 | 3 | 0 | 72 |
| Modularforms/DimensionFormulas.lean | 726 | 2 | 3 | 34 | 9 | 3 | 1 | 113 |
| HeckeRIngs/GLn/Projection.lean | 527 | 41 | 84 | 12 | 6 | 4 | 0 | 83 |
| HeckeRIngs/GL2/HeckeT_p_Gamma0.lean | 681 | 35 | 138 | 26 | 8 | 2 | 0 | 95 |
| Modularforms/PeterssonInnerProduct.lean | 836 | 24 | 193 | 63 | 6 | 1 | 0 | 91 |

*(~60 further closure files are small/clean — <300 lines, ≤1 long proof, negligible comments — and need no structural work.)*

## Part 2: Cross-file notes

- The closure was computed via transitive `import`/`public import` from `SMOObligations`. The five megafiles are the spine; the `Modularforms/*` leaves (eta, csqrt, exp_lems, …) are clean utilities.
- Two new clean modules from the recent refactor: `Unified/NebentypusHeckeRingHom.lean` (Φ_χ) and `Unified/EigenformFromRing.lean`.
- **Out-of-closure / broken-at-HEAD (not part of SMO, not in the build target):** 14 unmodified files importing the missing `SpherePacking.*` package (`Modularforms/{CuspFormIsoModforms, EisensteinBase, logDeriv_lems, Lv1Lv2Identities}`, `Modularforms/FG/*`, `Modularforms/SummableLemmas/*`) plus the untracked WIP `ForMathlib/HungerbuhlerWasem/ExitTimeExcision.lean`. These do not compile and should be excluded from any cleanup run.

---

## Recommended Action Plan (cleanup-led)

### Priority 1 — `/split-file` the megafiles (do FIRST; everything else depends on it)
The 1000-line guideline is exceeded by 21 files; five are pathological:
1. **`Newforms.lean` (19,131 L, 533 decls)** — split into focused modules (eigenform/newform basics, level-raise comm, the bad-prime Atkin–Lehner block, the q-expansion/Fourier block, the multiplicity-one inputs). Also has ~6,500 block-comment lines — much is recoverable.
2. **`AdjointTheory.lean` (17,704 L, 537 decls)** — split the Petersson-adjoint `petN_heckeT_p_*` development from the trace/spectral material.
3. **`BlockBijection.lean` (9,398 L)** — split the `fiber_block_form_*` and `heckeMultiplicity_*` chains; ~1,950 block-comment lines.
4. **`SMOObligations.lean` (6,462 L)** — split the descent (`descendCosetList_*`), the Miyake 4.6.x chain, and the final route-B SMO theorems.
5. **`CongruenceHecke.lean` (5,814 L)** — split the Γ₀ double-coset combinatorics from the Shimura-3.20/3.35 polynomial-presentation lane.

### Priority 2 — `/decompose-proof` the over-long proofs (128 over 100 lines, 517 over 50)
Concrete worst offenders (span; name; line):
- **SMOObligations**: `miyake_4_6_7_squarefree_decomp_with_lower_level` (517 L), `m6_2_extra_rep_levelRaise_bridge` (221), `miyake_4_6_14_delta_slash_sum_coeff_zero` (197 — **contains the protected term-mode patches; decompose around them, do not touch them**), `miyake_4_6_5_iterated_helper_general` (184), `miyake_4_6_8_inductive_step` (132).
- **BlockBijection**: `fiber_block_form_preimage_corrected_j_explicit` (325), `…_corrected_j` (301), `hfib_col_div_b_via_i_block_explicit` (230), the three `heckeMultiplicity_*_diagMat*` (205/204/187).
- **AdjointTheory**: `h_LHS_dist_eq_RHS_absorbed_of_M_infty_iUnion` (261) and the `petN_heckeT_p_adjoint_standard_form_*` family (126–149).
- **Newforms**: `heckeT_n_levelRaise_comm` (247) and ~20 `Newform.*` proofs of 120–311 L.

### Priority 3 — comment cleanup (folded into per-file `/cleanup`)
- **Block-comment bloat**: Newforms (~6,500 lines in `/- … -/`), BlockBijection (~1,950), LFunction (777), AtkinLehner (757), ConductorTheorem (683), PeterssonLevelN (661). Much is dev-history / proof-recipe prose to strip (keep statement docstrings + literature citations).
- **Narrative `--` lines (1,754 total)**: heaviest in Newforms (651), NebentypusHeckeRingHom (104), PSL2Action (103), HeckeT_p_GLpair (108), QExpansionSlash (99), PolynomialRing (82), HeckeT_p (80).

### Priority 4 — `/cleanup-all` golf pass (after P1–P2)
Once the megafiles are split and the giant proofs decomposed, per-file `/cleanup` golf (the standard 7-phase pass) becomes tractable file-by-file. Run it largest-remaining-first.

---

## Part 3: Mathlib API audit (summary — full per-decl audit deferred to per-file `/cleanup`)

The recent refactor already addressed the biggest API-structure issue: Hecke operators are now the image of the ring hom `heckeRingHomCharSpace : 𝕋(Γ₀(N)) →+* End(Mₖ(Γ₁(N),χ))`, so commutativity/multiplicativity come from the (commutative) Hecke ring rather than ad-hoc coset combinatorics, and the eigenform definition records its eigen-condition via that map. The q-expansion ↔ operator API (`fourierCoeff_heckeT_n`, `eigenvalue_eq_fourierCoeff`, …) already exists. A full per-declaration mathlib-API sweep across 95 files is impractical upfront and is exactly what the per-file `/cleanup` Phase-4 (five-method search) does — defer it there.

## Part 4: Moral duplications (summary)

The historical big duplication — the abstract Hecke ring vs. the concrete `heckeT_n` operators as parallel "islands" — is now **bridged** (`heckeRingHomCharSpace_D_p_eq_heckeT_p_all`, `heckeT_n_cusp_eq_heckeRingHom`). Within-file repeated proof patterns (the `heckeMultiplicity_*` triples in BlockBijection, the `petN_heckeT_p_adjoint_standard_form_*` family in AdjointTheory, the `fiber_block_form_*` pair) are candidates for parameterized helpers — best surfaced during the P2 decompositions, where the shared structure becomes visible.

## Part 5: Generalization (summary)

The χ-nebentypus development is now general (arbitrary `χ`). The GLn polynomial-presentation (Shimura 3.20) is proven for n=1,2 with the general-n case left as sorries (Phase B/C) — a deliberate scope boundary, not cleanup. No pressing field→ring style generalizations were flagged in the megafiles (they're already over `ℂ`/`ℤ` as the theory requires).

## Part 6: Junk / removable

- **SpherePacking-orphan files (14) + the untracked WIP `ExitTimeExcision.lean`** (Part 2): broken at HEAD, outside the build; either wire in the `SpherePacking` dependency or exclude/remove. Not SMO's concern.
- **Pre-existing sorries**: Newforms (2: L2550, L4472), BlockBijection (1: L8488 architectural), Projection (4, general-n), PolynomialRing (2, general-n). SMO is axiom-clean independent of these; close them only if the GLn general-n development is in scope.

---

## Scope note (honest)

This is a **metrics-driven, cleanup-targeted** overview (per the stated emphasis), not a full per-declaration inventory of all 95 files / 108K lines — that volume is impractical to inventory upfront, and the per-declaration mathlib/duplication/generalization analysis is performed file-by-file by `/cleanup` Phase 4 anyway. The deliverable here is the **prioritization**: which files to split, which proofs to decompose, where the comment bloat is — enough to drive `/cleanup-all` effectively.

## Top 5 actions

1. `/split-file` `Newforms.lean` (19K) and `AdjointTheory.lean` (17.7K) — the two are 35% of the closure.
2. `/decompose-proof` the 128 proofs >100 lines, starting with SMO's `miyake_4_6_7_squarefree_decomp_with_lower_level` (517 L) and BlockBijection's `fiber_block_form_preimage_corrected_j_explicit` (325 L).
3. Strip block-comment bloat in Newforms (~6.5K lines), BlockBijection (~2K), and the Eigenforms/Modularforms big files.
4. After P1–P2, run `/cleanup-all` largest-first over the (now-split) closure for golf + the per-declaration mathlib/duplication audit.
5. Decide the fate of the 14 SpherePacking-orphan files (wire-in vs exclude) so the build target is well-defined for cleanup.
