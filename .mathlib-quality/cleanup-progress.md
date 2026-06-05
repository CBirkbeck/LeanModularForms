# /cleanup campaign — file-by-file, full 10-phase runs (started 2026-06-05)

User directive: "go file by file, run /cleanup fully, dont skip any phases."

Baseline at start: `lake build LeanModularForms` green at commit 720d950 (hecke-ring).
Scope: all 222 project .lean files EXCLUDING `LeanModularForms/Chapters/` and
`LeanModularForms/Blueprint.lean` (Verso markup, not mathlib-style code).
Order: tranche-wise, upstream-first within tranche. One full /cleanup (phases 0–7) per file,
commit per file after Phase 7.

## Tranche 1 — ring-first refactor tree (newest code, never cleaned)

| # | File | LOC | Status |
|---|------|-----|--------|
| 1 | HeckeRIngs/GL2/Unified/Core.lean | 88→79→0 | cleaned, then **DELETED 2026-06-05** (dead subtree) |
| 2 | HeckeRIngs/GL2/Unified/NebentypusSpace.lean | 59→0 | cleaned, then **DELETED 2026-06-05** |
| 3 | HeckeRIngs/GL2/Unified/Gamma1CharSpace.lean | 82→81→0 | cleaned, then **DELETED 2026-06-05** |
| 4 | HeckeRIngs/GL2/Unified/TwistedSlash.lean | 95→0 | **DELETED 2026-06-05** (audit found subtree dead) |
| 5 | HeckeRIngs/GL2/Unified/CuspNebentypusSpace.lean | 186→0 | **DELETED 2026-06-05** |
| 6 | HeckeRIngs/GL2/Unified/TwistedHeckeRing.lean | 1249 | IN PROGRESS |
| 7 | HeckeRIngs/GL2/Unified/Gamma0RingDn.lean | 783 | queued |
| 8 | HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean | 1420 | queued |
| 9 | HeckeRIngs/GL2/Fricke.lean | 491 | queued |
| 10 | HeckeRIngs/GL2/Unified/ShimuraHom.lean | 449 | queued |
| 11 | HeckeRIngs/GL2/Unified/RingTransport.lean | 324 | queued |
| 12 | HeckeRIngs/GL2/Unified/DirectHeckeRing.lean | 178 | queued |
| 13 | HeckeRIngs/GL2/Unified/EigenformFromRing.lean | 102 | queued |

**SUBTREE DELETION (2026-06-05, user-approved):** files 1–5 (the GoodHeckeFamily/Γ₀-model
experimental layer, ~500 LOC) deleted as dead code — zero external consumers, zero blueprint
refs, superseded by the ring-first architecture. TwistedHeckeRing's vestigial
`import …Unified.TwistedSlash` rewired to `import …HeckeRingHomCharSpace`. Full build green.
Surviving artifact: `instance (n : coprimeToN N) : NeZero (n : ℕ)` in
HeckeRingHomCharSpace_General.lean:84 (extracted during file-3 cleanup; General's 3 redundant
haveI sites sweep in its tranche-2 run). The file-1/2/3 cleanup commits (b9702bc, 18e55d8,
3fd25b8) document the workers' audits; their mathlib finding (conjEnd = LinearEquiv.conjRingEquiv)
still applies to the LIVE files HeckeT_p_CharSpace_Comm.lean + ShimuraHom.lean (their runs).

## Tranche 2 — rest of HeckeRIngs/GL2 (queued, order TBD upstream-first)
HeckeRingHomCharSpace.lean (99), HeckeRingHomCharSpace_General.lean (108),
HeckeT_p_CharSpace_Comm.lean (87), HeckeT_p_GLpair.lean (127), HeckeT_p_Gamma0_Bridge.lean (39),
Prop334_HeckeSlashDiag.lean (32), Prop334_HeckeSlash.lean (138), LevelEmbed.lean (62),
HeckeT_p.lean (1004), HeckeT_p_Gamma0.lean, HeckeT_n.lean (1138), MultiplicationTable.lean (1135),
HeckeActionGeneral.lean (652), HeckeModularForm.lean (557), CharacterDecomp.lean (515),
AdjointTheory.lean (533) + AdjointTheory/ subdir, AdjointTheoryPetersson.lean (850),
FourierHecke.lean (789), LevelRaise.lean (598), Newforms/ subdir, …

## Tranche 3 — HeckeRIngs/GLn + AbstractHeckeRing
## Tranche 4 — Modularforms, Eigenforms, SMOObligations
## Tranche 5 — ForMathlib

## Per-file log

### 3. GL2/Unified/Gamma1CharSpace.lean (82 → 81 lines) — 2026-06-05
- Phases 0–7 all run; 7 declarations, 7 workers, all gates pass; build green ×3.
- NEW `instance (n : coprimeToN N) : NeZero (n : ℕ)` — born in this file's worker pass, then MOVED by /simplify-altitude to its true home next to `coprimeToN` (HeckeRingHomCharSpace_General.lean:84) so the whole import cone benefits. Killed 4 `letI`/`haveI` here.
- **4 renames applied (Phase 5b)**: `*_commute_from_mulFormula` → `*_commute` (×2 ambient + heckeT_coprimeRestrict), `*_commute_apply_from_mulFormula` → `*_commute_apply`, `modFormCharSpaceFamily_apply` → `modFormCharSpaceFamily_op` (proof-source suffixes violate name-what-is-proved; _op matches transport_op precedent). 1 external call site updated (CuspNebentypusSpace.lean:53). Queue truncated after apply.
- commute theorem: 5-line tactic proof (2 letI + show + rw/exact) → 1-line bare term (defeq Commute). All docstrings de-narrativized; ~10 redundant `(N := N)` named args dropped; header + module docstring normalized.
- **Campaign notes:** CuspNebentypusSpace.lean (file 5) now has 5 redundant `letI : NeZero …` sites (33, 68, 92, 93, 112 — instance covers them; the m*n product letI at 94–95 stays) + its own 3 `_from_mulFormula` renames to queue + Set.ext copy-proof golf. HeckeRingHomCharSpace_General.lean's 3 haveI sites (89, 102–103) also now redundant (instance is local there) — its tranche-2 run sweeps them.

### 2. GL2/Unified/NebentypusSpace.lean (59 → 59 lines) — 2026-06-05
- Phases 0–7 all run; 3 declarations + 1 new API lemma; 3 workers, all gates pass; build green ×3.
- Header normalized; module docstring rewritten (stale "experimental/isolated from SMO path" → Main definitions).
- NEW `@[simp] gamma0NebentypusChar_apply` (API-completeness; lets downstream stop unfolding the def by name).
- `gamma0NebentypusChar` now genuinely NeZero-free; `↥(Gamma0 N)` → `Gamma0 N`; noncomputable confirmed genuine (Gamma0MapUnits dep).
- Submodule copy-proof: `by ext f; simp […, gamma0NebentypusChar]` → term-mode `Set.ext fun f ↦ by simp [modFormCharSpace_iff_nebentypus, isNebentypus_iff]` (semicolon chain gone, redundant unfold-hint dropped).
- /simplify: variable/omit inversion fixed — `variable {N : ℕ}` + mid-file `variable [NeZero N]` split replaces 2–3 `omit` lines (note: an `omit` before a decl whose BODY needs the instance is a silent no-op — signature keeps the instance; verified via hover).
- mem_…_iff docstring de-staled. Renames queued: 0.
- **Campaign notes:** TwistedSlash.lean L36/37/57/58 + CuspNebentypusSpace.lean L132 carry now-redundant `gamma0NebentypusChar` simp unfold-hints (drop in their runs); CuspNebentypusSpace's `cuspGamma0NebentypusSubmodule` copy-proof can take the same Set.ext golf. PRE-EXISTING compiler PANICs (info-level, replayed) in ForMathlib/Seg1FTCProvider.lean:326 + Seg4FTCProvider.lean:343 (LCNF ExplicitBoxing) — investigate in tranche 5.

### 1. GL2/Unified/Core.lean (88 → 79 lines, −10%) — 2026-06-05
- Phases 0–7 all run; 11 declarations, 11 individual workers, all gates pass; full build green ×3.
- Header normalized (placeholder → Chris Birkbeck); module docstring rewritten (stale "experimental" prose → Main definitions).
- All 4 GoodHeckeFamily fields docstring'd (kills the only runLinter finding); structure docstring tightened; map_mul_of_coprime' field repacked to 99 chars.
- **conjEnd + conjEnd_apply/_one/_mul DELETED** — exact duplicate of mathlib `LinearEquiv.conjRingEquiv` (Algebra/Module/Equiv/Basic.lean:570, @[simps!]); `transport` migrated (`op n := e.conjRingEquiv (F.op n)`, commute' via `Commute.map`), vestigial `noncomputable` dropped, two `show`-laden proofs collapsed to one-liners.
- Added unapplied API companion `transport_op` (@[simp] — clean LHS; transport_apply untagged per bad-normal-form rule, `e` duplicated on RHS).
- /simplify pass: dead `open scoped MatrixGroups ModularForm` removed; `→+*` ascription dropped; simp-tag swap (above).
- Renames queued: 0. 
- **FLAGGED for user (big-change lane, NOT applied):**
  - Generalise `GoodHeckeFamily` to `[CommSemiring R] [AddCommMonoid V] [Module R V]` and drop `[NeZero N]` (all verified-compiling by the structure worker; public-API restatement, 2 consumer files).
  - Bundle `transport` as an equiv `GoodHeckeFamily N V ≃ GoodHeckeFamily N W` (altitude reviewer; 1 call site).
- **Campaign notes for later files:** `conjEndCharSpaceOne`/`conjEndRingHomCharSpaceOne` (HeckeT_p_CharSpace_Comm.lean:53,60) and `conjEndFricke`/`conjEndRingHomFricke` (Unified/ShimuraHom.lean:54,61) are the same conjRingEquiv pattern — migrate when those files are processed. `GoodIndex` kept (3-file vocabulary abbrev). Import `HeckeRingHomCharSpace_General` is heavier than Core's body needs but the sole consumer needs it anyway (report-only). Pre-existing info-note: ArcContribution.lean:44 `ring` → "Try this: ring_nf" (tranche 5).
