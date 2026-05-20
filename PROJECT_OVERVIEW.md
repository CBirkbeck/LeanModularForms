# Project Overview: LeanModularForms-hecke

Generated: 2026-05-20

## Executive Summary

LeanModularForms-hecke is a large Lean 4 / mathlib formalization of the Hecke
algebra and Atkin–Lehner / newform theory for modular forms on `Γ₁(N)`. It
covers (a) an **abstract Hecke ring construction** (`HeckeRIngs/AbstractHeckeRing/`)
following Shimura's Chapter 3, (b) **`GL₂`-specific Hecke operators** with the
multiplicative structure on `T_p`, `T_n`, the diamond action, the σ_p adjoint, the
Petersson inner product, and the conductor / new‐ vs. old‐form decomposition, plus
(c) a **`GL_n`-flavoured polynomial-ring scaffold**. The capstone is the recent
**strong multiplicity one theorem** (axiom-clean, only `propext, Classical.choice,
Quot.sound`), packaged in `Eigenforms/Newforms.lean` and re-exported with a
`Γ₀(N)+χ`-style transport layer in `Unified/Downstream.lean`.

Across 144 `.lean` files and ~141K LOC, the project is structurally sound and
modern in style (no `sorry`s outside ~16 deferred tickets, no manual ε-δ, slash
actions via mathlib's `SlashAction` etc.). The main improvement axes are
**ergonomic**: there is a large amount of duplication produced by the Γ₁ / Γ₀ /
GL-pair surface layering, several `_general` / `_strong` strict generalisations
that obsolete their predecessors, and a 13 000-line bypassed σ_p Q-permutation
chain in `AdjointTheory.lean` (T024 DSDoubleCosetTileBridge) that has been
superseded by the symmetric-form chain.

Top priorities (in descending value/risk ratio):
**(1)** archive `Prototype.lean`, `uniformcts.lean`, and trim the σ_p T024 dead
branch (≈ 13 K LOC removed); **(2)** add a `ModularForm.cast` API and `Gamma0MapUnits`
simp closure to land ~100 line savings in `MainLemma.lean` / `SMOObligations.lean`;
**(3)** generalise `𝕋 P ℤ` away from `ℤ` to any `CommSemiring`, which cascades
through `Ring.lean`, `Module.lean`, `Degree.lean`, `Commutativity.lean`,
`DiagonalCosets.lean`; **(4)** upstream the four `MeasureTheory.IsFundamentalDomain`
quartet, the four `charDecomp_*` joint-eigenvector lemmas, and the
`ForMathlib_*` files to mathlib.

## Statistics

- Files: **144** `.lean` files
- Lines: **~141 000** total LOC
- Top files by size:
  - `HeckeRIngs/GL2/AdjointTheory.lean` — 24 608 LOC (≈ 13 K of which is the
    T024 dead branch)
  - `HeckeRIngs/GL2/Newforms.lean` — 19 087 LOC
  - `SMOObligations.lean` — 11 530 LOC
  - `HeckeRIngs/GL2/BlockBijection.lean` — 9 800 LOC
  - `HeckeRIngs/GLn/CongruenceHecke.lean` — 6 500 LOC
- Sorries: **16** (1 in `BlockBijection`, 2 in `Newforms`, 2 in `AdjointTheory`, 3
  in `FG`, 1 in `Derivative`, 4 in `Projection`, 2 in `PolynomialRing`, 8 in
  orphan `AbstractHeckeRing/Prototype.lean`, 1 misc — note the Prototype 8 will
  vanish on deletion, taking the visible count down to ~8)
- Duplications: **31+ pairs** identified (across 18 sections)
- Generalization opportunities: **25**
- API gaps: **72** (17 missing lemmas + 15 missing `@[simp]` + 10 missing
  instances + 15 API completeness gaps + 15 awkward workarounds)
- Junk candidates: ~50 declarations + 3 file-level + 1 13 K-line dead branch,
  total estimated reduction **~14 500 LOC** (≈ 10 % of bulk)
- Axiom-clean theorems: `strongMultiplicityOne_axiom_clean` ✓
  (`propext, Classical.choice, Quot.sound`)

## Part 1: Declaration Inventory (Cross-Reference)

Inventory reports live in `/tmp/overview_reports/` (one per file). The 144
project files break down by directory as:

- **`Modularforms/`** — 69 files. Eisenstein-series, Δ, FG, Petersson, L-function,
  q-expansion, MLDE, dimension formulas. See `Modularforms_*.md`.
- **`HeckeRIngs/`** — 69 files split into:
  - `AbstractHeckeRing/` (9 files) — the polymorphic Hecke ring API
    (`Basic`, `Multiplication`, `Ring`, `Module`, `Associativity`, `Commutativity`,
    `Degree`, plus the orphan `Prototype.lean`).
  - `GL2/` (45 files) — `T_p`, `T_n`, diamond, character spaces, Atkin–Lehner,
    `AdjointTheory`, `Newforms`, `Unified/` transport layer, `BlockBijection`.
    See `HeckeRIngs_GL2_*.md`.
  - `GLn/` (15 files) — diagonal cosets, coprime multiplicativity, congruence Hecke,
    polynomial ring, projection. See `HeckeRIngs_GLn_*.md`.
- **`Eigenforms/`** — 6 files (`AtkinLehner`, `AtkinLehnerProjection`,
  `ConductorTheorem`, `HeckeLemma`, `MainLemma`, `TraceOperator`).
- **`SMOObligations.lean`** — 1 file (project root); a long M1-…-M8 ticket
  decomposition of Miyake §4.6's strong multiplicity one descent.

Note: `/tmp/overview_reports/` contains a benign duplicate: both
`HeckeRIngs_AbstractHeckeRing.md` and `HeckeRIngs_AbstractHeckeRing_root.md`
inventory the same `LeanModularForms/HeckeRIngs/AbstractHeckeRing.lean` root facade.
Drop one to bring the count to 144.

## Part 2: Cross-File Dependencies

High-level import graph (top→bottom = high-level → foundation):

```
SMOObligations.lean
   │   (Miyake §4.6 ticket-decomposed multipass)
   ▼
Eigenforms/{Newforms, MainLemma, AtkinLehner, ConductorTheorem,
            HeckeLemma, TraceOperator, AtkinLehnerProjection}
   │
   ▼
HeckeRIngs/GL2/{Unified/Downstream, Newforms (canonical),
                 AdjointTheory, BlockBijection, LFunction (under Modularforms)}
   │
   ▼
HeckeRIngs/GL2/{HeckeT_p, HeckeT_n, HeckeT_p_Gamma0, HeckeT_p_Gamma1,
                HeckeT_p_GLpair, HeckeT_p_CharSpace_Comm,
                HeckeModularForm, HeckeModularForm_Gamma0,
                FourierHecke, LevelRaise, CharacterDecomp,
                CharSpaceIso, Gamma1Pair, BadPrimeDoubleCoset,
                HeckeAction, HeckeActionGeneral, HeckeSlashExplicit,
                CongruenceIndex, DeltaEigenform}
   │
   ▼
HeckeRIngs/AbstractHeckeRing/{Basic, Multiplication, Ring, Module,
                              Associativity, Commutativity, Degree}
   │
   ▼
HeckeRIngs/GLn/{Basic, DiagonalCosets, CoprimeMul, PolynomialRing,
                CongruenceHecke, ...}
   │
   ▼
Modularforms/{PeterssonLevelN, PeterssonInner, LFunction,
              CharacterDecomp, ConductorTheorem, qExpansion_lems,
              Delta, EisensteinBase, Derivative, FG, DimensionFormulas,
              SerreDerivativeSlash, AtImInfty, ForMathlib_*,
              upperhalfplane, eta, summable_lems, tendstolems}
   │
   ▼
mathlib (Modular forms, GL₂, Slash, Fundamental domain, Periodic, qParam,
         Module.End.maxGenEigenspace, …)
```

Highest-fan-in consumer relationships:

- `HeckeT_p_Gamma0_Bridge.lean` re-exports private helpers from
  `HeckeT_p_Gamma0.lean` for `AdjointTheory.lean` (three "identical" private
  lemmas — see Part 4 row §2).
- `Eigenforms/Newforms.lean` is the canonical entry point for strong
  multiplicity one; `Unified/Downstream.lean` re-exports it via the
  `Γ₀(N), χ`-style submodule. Both shapes are needed by downstream proofs.
- `AdjointTheory.lean` is the largest cross-file fan-out hub: consumed by
  `Newforms.lean` (σ_p adjoint), `PeterssonLevelN.lean`, `LFunction.lean`,
  `BlockBijection.lean`.

## Part 3: Mathlib API Audit

Source: `/tmp/overview_reports/PHASE2_mathlib_audit.md`.

**Top issues**

- 9 ergonomic duplicates of mathlib (e.g. `pnat_div_upper`, the seven `ForMathlib_*`
  + `AtImInfty.lean` + `tendstolems.lean` + `upperhalfplane.lean` + commented-out
  `uniformcts.lean` cluster, `HeckeCoset_ext_toSet` reduplicated in
  `Multiplication.lean`, `smulOrbit_map_inj` reduplicated in `Degree.lean`).
- 6 generalization opportunities (the abstract Hecke ring `𝕋 P ℤ` should be
  `𝕋 P Z` for any `CommSemiring Z`, `HasDetOne` should be `HasDetPlusMinusOne`,
  the four `MeasureTheory.IsFundamentalDomain.*` quartet, the four `charDecomp_*`
  joint-eigenvector lemmas, the `qKerBelow` Artinian stabilisation, the
  `monoidHomSlashAction` over `GL₂(F) → GL₂(ℝ)` for arbitrary subring `F ≤ ℝ`).
- 8 hand-rolled patterns with mathlib analogues (`summable_lems.lean`,
  `tendstolems.lean`, `D₂` cocycle aliases, q-expansion convergence at the cusp,
  `IsBoundedAtImInfty.neg`, `mapGL_injective` chain, `ZMod.unitOfCoprime` character
  multiplicativity, `heckeT_p_preserves_cuspFormCharSpace` placeholder stub).

**Top 5 recommendations** (from the audit)

1. Inline / delete the seven scratch / for-mathlib small files
   (`ForMathlib_UpperHalfPlane`, `ForMathlib_SlashActions`,
   `ForMathlib_FunctionsBoundedAtInfty`, `AtImInfty`, `tendstolems`,
   `upperhalfplane`, `uniformcts`) plus `AbstractHeckeRing/Prototype.lean`. Low
   risk, removes a `sorry`-bearing file.
2. Replace `IsSupportedOnDvd` by `PowerSeries.expand` (the standard mathlib
   formalisation of "supported on multiples of `d`"). Medium risk: pervasive in
   `Newforms.lean`, `MainLemma.lean`, `LevelRaise.lean`.
3. Upstream the abstract `charDecomp_*` joint-eigenvector lemmas
   (`CharacterDecomp.lean` lines 76–149). Low risk, pure mathlib PR.
4. Tag the `MeasureTheory.IsFundamentalDomain.*` quartet for upstream
   (`PeterssonLevelN.lean` lines 304–490; 60+ references in
   `AdjointTheory.lean`). Low risk.
5. Generalise `𝕋 P Z` away from `ℤ`. Medium-to-high risk but mechanical —
   `(Z : Type*) [CommSemiring Z]` in place of `ℤ` throughout `AbstractHeckeRing`.

## Part 4: Moral Duplications

Source: `/tmp/overview_reports/PHASE2_duplication.md`. 31+ pairs identified across
18 sections; top 15 verdict rows:

| Pair | Verdict |
|------|---------|
| `pnat_div_upper` (`upperhalfplane.lean:13`) vs (`SummableLemmas/Basic.lean:54`) | UNIFY |
| `pos_nat_div_upper` (same two files) | UNIFY |
| `smulOrbit_map_inj` (`Degree.lean:37`, private) vs `smulOrbit_map_injective` (`Associativity.lean:13`, private) | UNIFY — promote to non-private once |
| `pSupportedProjection` (new `AtkinLehnerProjection.lean:15`) vs older copies in `AtkinLehner.lean:1040` and `TraceOperator.lean:447` | DELETE_OLDER |
| `miyake_V_p_descend_identity` vs `_with_char` (SMOObligations) | DELETE_OLDER |
| `miyake_4_6_7_squarefree_decomp` vs `_with_lower_level` (SMOObligations) | DELETE_OLDER — 692 LOC |
| `descendExtraGamma_spec'` vs `descendExtraGamma_spec` (private, both in SMOObligations) | UNIFY |
| `cuspForm_restrictSubgroup_mem_cuspFormCharSpace` (SMOObligations, private) vs `restrictSubgroup_mem_modFormCharSpace` (MainLemma) | DELETE_WRAPPER |
| `adj_diag_1p_eq_T_p_lower_bridge` (`HeckeT_p_Gamma0_Bridge.lean`) vs `adj_diag_1p_eq_T_p_lower` (`HeckeT_p_Gamma0.lean`, private) | UNIFY — promote private |
| `adj_rep_mem_D_p_Gamma0_bridge` vs `adj_rep_mem_D_p_Gamma0` (same files, both private) | UNIFY |
| `GL_adjugate_mem_D_p_Gamma0_bridge` vs `GL_adjugate_mem_toSet_Gamma0` (same files, private) | UNIFY |
| `doubleCoset_eq_of_mem'` (`GL2/Basic.lean:75`, private) vs (`GLn/CoprimeMul.lean:80`, private) vs `HeckeCoset.doubleCoset_eq_of_mem` (`AbstractHeckeRing/Basic.lean:161`) | UNIFY — both private should call abstract |
| `pSupportedProjection_apply` / `_zero` (older vs newer copies) | DELETE_OLDER |
| `Prototype.lean` entire file vs corresponding `Basic.lean`/`Ring.lean` decls | DELETE — design draft, 273 LOC, 8 sorries |
| Inventory metadata: `HeckeRIngs_AbstractHeckeRing.md` vs `HeckeRIngs_AbstractHeckeRing_root.md` are byte-identical | DELETE_OLDER (one of the reports) |

**KEEP_BOTH** pairs (Γ₀ / Γ₁ / GL-pair surface layering) make up the rest of the
duplication report; these are by design (callers need the subgroup-specific
surface) and are candidates for a future polymorphic-over-`H ≤ GL_pair` refactor,
not for deletion.

## Part 5: Generalization Opportunities

Source: `/tmp/overview_reports/PHASE2_generalization.md`. 25 candidates. Top 10
ordered by payoff / risk:

| # | Candidate | Difficulty |
|---|-----------|-----------|
| 1 | `𝕋 P Z` for any `CommSemiring Z` (cascades into 2, 3, 17, 22) | Medium |
| 6 | `FiniteTileFundamentalDomain` — promote to mathlib | Low |
| 7 | `IsFundamentalDomain.subgroup_iUnion_out_smul` quartet — promote to mathlib | Low |
| 11 | `charSpace_directSum` over any finite-group representation (the abstract section is already polymorphic) | Low |
| 2 | `deg : 𝕋 P R →+* R` for any `CommRing R` (falls out of #1) | Low |
| 3 | `T_single_*` API over any `CommSemiring` | Low |
| 17 | `T_diag_span` over `CommSemiring` (after #1) | Low |
| 22 | `AntiInvolution`-derived `CommRing` over any coefficient ring (after #1) | Low |
| 13 | `lCoeff`/`lSeries`/abscissa bounds over arbitrary `[Γ.IsArithmetic]` | Low |
| 4 | `peterssonInner` for any `[Γ.IsArithmetic]` (`SL(2,ℤ)` specialisation removable) | Medium |

Higher-difficulty candidates (not in the top 10):
- `levelRaise` over arbitrary `GL₂⁺(ℝ)` commensurator elements — High;
- `Eigenform` over arbitrary `Γ` with a `HeckeAction` typeclass — High;
- Level-`N` closed-form dimension formulas — High (open development).

## Part 6: API Improvements

Source: `/tmp/overview_reports/PHASE2_api_improvements.md`. 72 distinct items.
Top 15:

**Missing lemmas (8)**

1. `ModularForm.cast` API to replace the 8 private cast lemmas in
   `MainLemma.lean:1455-1965` (affects 25+ proofs in `MainLemma`,
   `SMOObligations`).
2. `Gamma0MapUnits_{one,mul,inv,val}` as `@[simp]` (30+ inline `Units.ext`
   rituals across `HeckeT_n`, `AdjointTheory`, `MainLemma`, `SMOObligations`).
3. `qExpansion_{add,sub,neg,smul}_Gamma1` wrappers that elide the
   `strictPeriods_Gamma1` witness boilerplate (30+ sites).
4. `heckeT_p_divN_apply` and `heckeT_p_all_apply_{coprime,not_coprime}`
   one-shot apply lemmas (30+ unfolding sites).
5. `coe_diamondOpCusp_eq_of_Gamma0MapUnits` abstract bridge — the 4 σ_p
   slash-as-diamond variants in `AdjointTheory.lean:429-582` become 1-liners
   (≈ 80 lines saved).
6. `IsCusp.smul_glMap` — recurring 20-line proof in `HeckeT_n.lean:131`,
   `AdjointTheory.lean:74-93`, `SMOObligations.lean:4360`.
7. `qExpansion_restrictSubgroup` as `@[simp]` (6 inline `change … ; rfl` in
   `MainLemma`).
8. `slash_neg_one_odd` companion for odd weights (`ForMathlib_SlashActions`).

**Missing `@[simp]` tags (4)**

9. `mapGL_coe_matrix` / `glMap_coe_matrix` (used inline 50+ times across all
   GL2 files).
10. `IsSupportedOnDvd.{add,sub,neg,smul,one}` (only `.zero` is tagged).
11. `peterssonAdj_peterssonAdj`, `peterssonAdj_det`, `peterssonAdj_coe`
    (involution + matrix-level equations).
12. `descendCosetCount_{pos, of_p_sq_dvd, of_not_p_sq_dvd}` (unfolded inline
    30+ times in `SMOObligations.lean`).

**Missing instances (3)**

13. `@[fun_prop]` on `MDifferentiable_D₂`, `F_holo`, `G_holo`, `L₁₀_holo`,
    `MDifferentiable_div` (composition friendliness).
14. `(Gamma1 N).map (mapGL ℝ)).IsArithmetic` — verify it is inferrable;
    otherwise expose explicitly.
15. `sum_slash` (`HeckeT_p.lean:163`) vs `sum_slash'` (`HeckeT_n.lean:86`,
    private): consolidate to the canonical public form.

## Part 7: Junk / Removable

Source: `/tmp/overview_reports/PHASE2_junk.md`. ~50 declarations + 3 file-level
+ 1 13 K-line dead branch. Total estimated reduction: ~14 500 LOC.

**Top items by category:**

- **A. Unused private/public helpers (~280 LOC)**
  - `T_p_lower_mul_upper`, `T_p_upper_mul_lower`, `crt_sum_swap`
    (`HeckeT_n.lean:622-700`)
  - `multipass_{int_castRingHom_unique, d_succ_eq_descendCosetCount,
    moebius_fin_p_well_defined, alpha_integer_entries_p_sq_dvd_N,
    descendExtraGamma_inverse, slash_eq_of_diamond_eq, slashSumOp,
    coprime_filter_extends_dvd}` (SMOObligations, 11 declarations)
  - `descendCosetList_orbit_identity` (SMOObligations:4386, 33 LOC)
  - `descendCosetList_moebius_inj` (SMOObligations:2644, 44 LOC)
  - `T_pp_eq_T_ad`, `T_ad_one_one`, `T_pp_comm_T_elem` (GL2/Basic, INVESTIGATE)
  - 5 unused public lemmas in `HeckeRingHomCharSpace_General.lean` (~70 LOC)

- **B. Wrappers around a single mathlib call**
  - `multipass_int_castRingHom_unique` is `Subsingleton.elim`
  - `mem_coprimeToN` is `Iff.rfl`
  - `heckeRingHomCharSpaceOne_apply` is `rfl`

- **D. Superseded by newer versions (~840 LOC)**
  - `miyake_4_6_7_squarefree_decomp` (692 LOC, superseded by `_with_lower_level`)
  - `miyake_V_p_descend_identity` (146 LOC, superseded by `_with_char`)

- **E. T024 dead branch (~13 000 LOC)**
  - `AdjointTheory.lean:9913-22929` — DSDoubleCosetTileBridge: the 14-layer
    scaffold (TileFormIntegralResidual / SigmaQPermResidual blocker
    abstractions, branch-by-branch reductions, FD-shift exchange variants,
    HeckeFD-swap residual chain, iUnion residuals, two-tile-shift residuals,
    two-FD-slash-exchanges, per-tile-balances, per-q-fd-balances) is now
    **bypassed by the symmetric-form chain** which short-circuits through
    `petN_heckeT_p_adjoint_standard_form_from_petN_symmetric_form`. Largest
    single LOC reduction in the project.

- **F. Commented-out / dead-variable cleanup (~150 LOC)**
  - `uniformcts.lean` — entire file commented out (79 LOC), DELETE FILE.
  - `logDeriv_lems.lean:27-93` — 67-line commented-out block, REMOVE.
  - `EisensteinBase.lean:82, 667-670` — dead `variable` declarations.
  - `ResToImagAxis.lean` — unused `_hc`, `_hn₀` hypotheses.
  - `SMOObligations.lean` — 11 `linter.unusedSimpArgs false in` opt-outs to
    audit.

- **H. Whole files for full deletion (~620 LOC)**
  - `AbstractHeckeRing/Prototype.lean` (273 LOC, 8 sorries, not imported)
  - `uniformcts.lean` (79 LOC, commented out)
  - `HeckeSlashExplicit.lean` (240 LOC, INVESTIGATE — interface/checkpoint?)

---

## Recommended Action Plan

### Priority 1: Quick Wins (can do now, low risk)

1. **Delete `AbstractHeckeRing/Prototype.lean`** (273 LOC, 8 sorries) — design
   draft superseded by `Basic.lean`/`Ring.lean`, not imported. Removes the
   only `sorry`-bearing file in the Hecke-ring core.
2. **Delete `Modularforms/uniformcts.lean`** (79 LOC) — entire file commented
   out, mathlib has the API.
3. **Delete superseded `miyake_4_6_7_squarefree_decomp` and
   `miyake_V_p_descend_identity`** (~840 LOC together, both explicitly marked
   "unused, superseded by `_with_lower_level`/`_with_char`").
4. **Delete the 11 unused `multipass_*` helpers and 3 unused `HeckeT_n` lemmas**
   (~150 LOC). These are explicitly flagged "unused in file".
5. **Unify the three `_bridge` private re-statements** in
   `HeckeT_p_Gamma0_Bridge.lean` by promoting the originals in
   `HeckeT_p_Gamma0.lean` to scoped/public (~30 LOC, eliminates 3 confusing
   identical pairs).
6. **Tag missing `@[simp]` lemmas**: `mapGL_coe_matrix`, `Gamma0MapUnits_val`,
   `IsSupportedOnDvd.{add,sub,neg,smul,one}`, `peterssonAdj_*` (15 simp tags
   to add).
7. **Remove the commented-out 67-line block in `logDeriv_lems.lean`** and the
   dead `variable` declarations in `EisensteinBase.lean` / `ResToImagAxis.lean`.

### Priority 2: API Improvements (significant impact)

1. **`ModularForm.cast` API** — extract the 8 private cast lemmas in
   `MainLemma.lean:1455-1965` into a public `CastLinearEquiv` + `_apply`,
   `_add`, `_smul`, `_sum`, `_neg`, `_zero`, `_qExpansion_coeff`,
   `_mem_modFormCharSpace` (mirrors the existing `castCuspFormLinearEquiv`).
   Affects 25+ proofs.
2. **`Gamma0MapUnits` simp closure** — add `_one`, `_mul`, `_inv`, `_val` as
   `@[simp]`. Removes inline `Units.ext` rituals in 30+ sites.
3. **`qExpansion_*_Gamma1` wrappers** — wrap the period-1 q-expansion arithmetic
   to elide the `strictPeriods_Gamma1`-witness boilerplate (5 lines per call ×
   30 sites = 150 LOC).
4. **`heckeT_p_divN_apply` and `heckeT_p_all_apply_*` one-shot lemmas** —
   collapses the recurring 2-step unfolding (30+ sites in `Newforms`,
   `MainLemma`, `SMOObligations`).
5. **Tag `@[fun_prop]` on `MDifferentiable_D₂`, `F_holo`, `G_holo`,
   `L₁₀_holo`, `MDifferentiable_div`** — composition friendliness.
6. **`coe_diamondOpCusp_eq_of_Gamma0MapUnits`** abstract bridge — the 4 σ_p
   slash-as-diamond variants in `AdjointTheory.lean:429-582` become 1-liners
   (~80 LOC saved).
7. **`IsCusp.smul_glMap` lemma** — promotes a recurring 20-line proof in
   `HeckeT_n.lean:131`, `AdjointTheory.lean:74-93`, `SMOObligations.lean:4360`
   to a public 1-liner.

### Priority 3: Generalizations (requires mathematical thought)

1. **`𝕋 P Z` over any `CommSemiring Z`** (cand. #1) — `(Z : Type*)
   [CommSemiring Z]` in place of `ℤ` throughout `AbstractHeckeRing/{Basic,
   Multiplication, Ring, Module, Associativity, Commutativity, Degree}.lean`.
   Cascades into candidates 2, 3, 17, 22 automatically. Mechanical but
   pervasive. Medium difficulty.
2. **`peterssonInner` over arbitrary `[Γ.IsArithmetic]`** (cand. #4) — the
   level-1 specialisation `peterssonInner_definite_levelOne` is the only piece
   that hardcodes `SL(2,ℤ)`. Removing it via `exists_smul_mem_fd` gives the
   natural setup for the Atkin–Lehner trace machinery. Medium.
3. **`charSpace_directSum` over any finite-group representation** (cand. #11)
   — no proof work needed; just reorganise. The abstract section
   `CharacterDecomp.lean:67-163` is already polymorphic. Low.
4. **`IsSupportedOnDvd` over any `Field`** (cand. #19) — purely module-
   theoretic; opens the door to `PowerSeries.expand` integration (Rec 2 of
   the mathlib audit). Low.

### Priority 4: Structural Changes (major refactoring)

1. **Excise the T024 dead branch** (`AdjointTheory.lean:9913-22929`,
   ~13 000 LOC) — the 14-layer DSDoubleCosetTileBridge scaffold is now
   bypassed by the symmetric-form chain. Largest single LOC reduction in the
   project, but requires confirming the symmetric-form chain is fully
   validated (currently 2 open sorries at lines 22929-23334).
2. **Upstream the four `MeasureTheory.IsFundamentalDomain.*` quartet** + the
   four `charDecomp_*` joint-eigenvector lemmas + the
   `FiniteTileFundamentalDomain` structure + the four `ForMathlib_*` files
   to mathlib. Pure migration with no proof work.
3. **Replace `IsSupportedOnDvd` by `PowerSeries.expand`** (mathlib audit
   Rec 2) — substantial rewrite across `AtkinLehner.lean`,
   `Newforms.lean`, `MainLemma.lean`, `LevelRaise.lean`; unlocks
   `expand_mul_eq_comp` and other ring-hom rules.
