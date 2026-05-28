# Project Overview: LeanModularForms-hecke

**Generated**: 2026-05-28 (branch `hecke-ring`)

**Note**: this overwrites a 2026-05-22 cleanup-audit file with the same name.
The earlier file (a `/cleanup-all` priority pass over the SMO closure) is in git
history; this is the full `/overview` pass covering the whole 185-file project.

**Scope of this pass.** The full `/overview` workflow specifies a per-declaration
inventory entry (What / How / Hypotheses / Uses / Notes) produced by parallel
sub-workers. This pass was executed by a single orchestrator without the Agent /
TaskCreate dispatch tool, so for ~5,400 declarations across 185 files an entry-per-decl
prose write-up was infeasible in one session. The inventory below is at the
**file / cluster level** with per-declaration name lists drawn directly from the
source, plus deep-dive per-decl entries for: (i) the headline result and its full
proof closure, (ii) every declaration carrying a `sorry`, (iii) the AbstractHeckeRing
foundation, and (iv) every result identified in the duplication, generalization, and
junk sections. The mathlib API audit and the moral-duplication / generalization /
junk findings are concrete with file:line citations and unification proposals.

---

## Executive Summary

This project develops a substantial chunk of the classical theory of modular
forms in Lean 4 / Mathlib, with **two distinct strands** that have largely been
developed in parallel and are only partially unified:

1. **Analytic modular-forms foundations** (`Modularforms/` cluster, ~19k LOC, 65
   files). Eisenstein series, the Δ function, Jacobi theta, η, the Petersson
   inner product (with the level-N variant `petN`), L-functions, Mellin
   transforms, and the analytic infrastructure (Cauchy primitives, residue
   theory, exit-time excision in `ForMathlib/`).

2. **Algebraic Hecke-ring theory** (`HeckeRIngs/` cluster, ~50k LOC, 86 files).
   The abstract `HeckePair` / `HeckeCoset` / `𝕋 P ℤ` formalism
   (`AbstractHeckeRing/`), the `GL_n` instance (`GLn/`, with the polynomial-ring
   structure and the SL₂(ℤ) Smith-decomposition surjection), the `GL₂(ℚ)`
   action on `M_k(Γ₁(N))` (`GL2/`), the `T_n` / `T_p` Hecke operators, and the
   character decomposition.

The Eigenforms layer (`Eigenforms/`, 6 files, ~8k LOC) and the SMO Obligations
layer (`SMOObligations/`, 8 files, ~5k LOC) bridge those two strands and
culminate in:

> **`HeckeRing.GL2.strongMultiplicityOne_constMul`** (Miyake Theorem 4.6.12),
> `SMOObligations/StrongMultiplicityOneFull.lean:1429`. **Headline result**:
> any common `T_n`-eigenfunction `g ∈ S_k(Γ₁(N),χ)` sharing the eigenvalues of a
> normalised newform `f` off a finite set is `g = c • f`. According to the
> project's recorded `#print axioms` audit (project memory, 2026-05-27), this
> theorem is axiom-clean
> `[propext, Classical.choice, Quot.sound]` — no `sorryAx` in the dependency
> closure. The companion `strongMultiplicityOne_axiom_clean_unconditional`
> (line 1466) recovers the both-newforms statement (DS 5.8.2.1) by forcing
> `c = 1` via normalisation.

### Top findings

1. **Major structural duplication: the `_unconditional` twins.** The SMO
   pipeline carries two complete copies of every assembly theorem — one with a
   `h_chi_factor` hypothesis (Miyake's character-conductor restriction), one
   without. After Gap #4 (the `cuspFormsOldChar_inf_charSpace_le_cuspFormsOld`
   reverse inclusion) was discharged, the conditional twins became corollaries
   of the unconditional ones, but both versions remain in the file. See P4-DUP-1.

2. **Junk cluster in `ConcreteFamily.lean` (~6,000 lines).** The
   `petN_heckeT_p_symmetric_form{,_doubleCoset,_global}` cluster (lines
   5471, 5499, 5519, 6015, 6037 and the dead `_aggregate_peeled_diagonal_balance`
   at 5490) is **superseded** by the trace-engine route
   `petN_heckeT_p_adjoint_via_trace`. `heckeT_p_adjoint` (line 5983) closes via
   the trace route, leaving the doubleCoset cluster — including the only
   remaining `sorry` in `ConcreteFamily.lean` — entirely dead. See P1-JUNK-1.

3. **The `Eigenforms/` and `HeckeRIngs/GL2/Newforms/` layers contain a parallel
   re-development of Atkin–Lehner / Main Lemma material.** Both clusters
   contain a `mainLemma`, a `newform_unique`, an `oldPart` API, and Atkin–Lehner
   projections, with substantial overlap. The `Newforms/MainLemma.lean`
   `mainLemma` (line 435) still carries `sorry` (the analytic-spectral
   character-free version), whereas the per-character `Eigenforms/`
   `mainLemma_charSpace_routeB` is complete. See P4-DUP-2.

4. **Mathlib API choice: many uses of `fun x => ...` should be `fun x ↦ ...`**
   (per the project's own arrow-style memory note). Raw counts: 1,221 `=>`
   lambdas vs 555 `↦` lambdas across the project. Mechanical fix-up is
   appropriate. See P1-API-1.

5. **`ForMathlib/` is empty of project glue.** The two files
   `ExitTimeExcision.lean` and `CauchyPrimitive.lean` are upstream-ready and
   the existing `LeanModularForms.Modularforms.ForMathlib_*` modules sit in
   the wrong location (under `Modularforms/`, not under `ForMathlib/`). See
   P3-STRUCT-1.

---

## Statistics

| Quantity                                  | Value     |
|-------------------------------------------|-----------|
| Lean files (excluding `.lake/`, `build/`) | **185**   |
| Total LOC                                 | 116,473   |
| Average file LOC                          | 629       |
| Strict top-level declarations             | 5,396     |
| Sorry-bearing files (live + dead)         | 8         |
| Live `sorry`s in build closure            | 2 (`Newforms/MainLemma.lean::mainLemma`, `Modularforms/Derivative.lean::antiSerreDerPos`) |
| Other `sorry`s (junk / context-specific)  | ~20+ — enumerated below |
| `set_option maxHeartbeats` overrides      | **0** (project policy enforced) |
| `set_option linter.*` overrides           | 2 (`DiagonalCosets.lean:794,809`) |
| `@[simp]` tags                            | 261       |
| `@[fun_prop]` tags                        | 41        |
| `@[ext]` tags                             | **1** (gap!) |
| `Set.Finite` mentions                     | 2 (low — good, `Finset` is preferred) |
| Hand-rolled `∃ M, ∀ ‖_‖ ≤ M` patterns     | 0 detected (good) |

**Per-cluster declaration counts** (sum of decl-head greps, includes private +
protected + noncomputable variants):

| Cluster                                   | Decls | Files |
|-------------------------------------------|------:|------:|
| `Modularforms/` + subdirs                 | 1,407 | 65    |
| `HeckeRIngs/AbstractHeckeRing/`           |   264 | 8     |
| `HeckeRIngs/GLn/` + subdirs               |   850 | 27    |
| `HeckeRIngs/GL2/` + subdirs               | 2,328 | 63    |
| `Eigenforms/`                             |   369 | 6     |
| `SMOObligations/`                         |   271 | 8     |
| `ForMathlib/`                             |    30 | 2     |
| **Total (cross-checked)**                 | **5,519** | **185** |

**Top 10 files by LOC** — all of these warrant individual cleanup attention:

1. `HeckeRIngs/GL2/AdjointTheory/ConcreteFamily.lean` — 6,052 lines
2. `HeckeRIngs/GL2/AdjointTheory/TileBridge.lean` — 4,352 lines
3. `HeckeRIngs/GL2/AdjointTheory/DeltaBSystem.lean` — 3,451 lines
4. `HeckeRIngs/GL2/AdjointTheory/FDTransport.lean` — 2,300 lines
5. `Eigenforms/MainLemma.lean` — 2,221 lines
6. `HeckeRIngs/GL2/HeckeT_n.lean` — 2,056 lines
7. `HeckeRIngs/GL2/AdjointTheory/SummandAdjoint.lean` — 1,945 lines
8. `HeckeRIngs/GLn/BlockBijection/SLReduction.lean` — 1,669 lines
9. `HeckeRIngs/GL2/Newforms/MellinBridges.lean` — 1,654 lines
10. `HeckeRIngs/GLn/CongruenceHecke/Surjectivity.lean` — 1,646 lines

Six of the top ten are in the AdjointTheory subtree, signalling that the
adjoint-spectral chain is the most expensive part of the development.

---

## Part 1: Declaration Inventory (by cluster)

### Cluster A: `HeckeRIngs/AbstractHeckeRing/` (foundation, 8 files, 264 decls)

**Module purpose.** Develops the abstract Hecke ring `𝕋 P ℤ` of a `HeckePair P
= (G, H, Δ)` (group `G`, subgroup `H`, sub-semigroup `Δ ⊇ H`), as the
`Finsupp (HeckeCoset P) ℤ`-valued double-coset algebra under the
"multiplicity" multiplication `m(g₁, g₂, d) = #{(i,j) | β₁ᵢ · β₂ⱼ ∈ d}`. The
abstract API is then specialised to `GLn` and `GL₂` Hecke pairs elsewhere.

| File | Lines | Purpose |
|------|------:|---------|
| `Basic.lean` | 401 | `HeckePair`, `dcRel`, `lcRel`, `HeckeCoset`, `HeckeLeftCoset`, `dcSetoid`, `lcSetoid`, `HeckeCoset.toSet`, `rep`, `mk_rep`, `ind`, `one`, `decompQuot` (= left-coset decomposition of a double coset) |
| `Multiplication.lean` | 764 | `mulMap`, `heckeMultiplicity`, `heckeMultiplicityMulMap`, `mulSupport`. Proves the multiplicity is well-defined on double-coset classes (`heckeMultiplicity_pos_of_mem_mulSupport`) and `m(g, 1, d)`, `m(1, g, d)` formulas needed for the unit law |
| `Module.lean` | 275 | `HeckeModule P Z := Finsupp (HeckeLeftCoset P) Z`, the `𝕋 P Z`-module via `smulOrbit`. Proves `HeckeModule P ℤ` is a faithful `𝕋 P ℤ`-module (`instFaithfulSMulHeckeModule`, line 270), which is what makes the multiplication well-defined |
| `Ring.lean` | 196 | Lifts the module structure to `Mul`, `One`, `Semiring`, `Ring` instances on `𝕋 P ℤ`; `T_single_mul_T_single` formula |
| `Associativity.lean` | 734 | Proves `mul_assoc` for `𝕋 P ℤ` via the "uniform shift" bijection (`heckeMultiplicity_uniform`, line 363); the file is long because the bijection is built explicitly and shown to commute with the multiplicity counting on both sides |
| `Commutativity.lean` | 491 | `AntiInvolution P` structure (an order-reversing bijection of `G` fixing `H` and `Δ`); the theorem `mul_comm_of_antiInvolution` (line 471) that if every double coset is `ι`-fixed then `𝕋 P ℤ` is commutative; `instCommRing_of_antiInvolution` (line 487) |
| `Degree.lean` | 262 | `HeckeCoset_deg D := number of left H-cosets in D` (a positive integer); ring homomorphism `deg : 𝕋 P ℤ →+* ℤ` (line 197); `deg_mul` (line 216) |
| `Prototype.lean` | 272 | **Replaced/superseded prototype**. Contains 9 `sorry`s — see Junk list below. Not imported by the live `AbstractHeckeRing.lean` aggregator |
| `AbstractHeckeRing.lean` | 25 | Aggregator: imports the 7 live submodules |

**Headline (cluster A)**:
`HeckeRing.HeckeCoset_deg` + the ring-homomorphism property + `mul_comm_of_antiInvolution`.

**Headline-decl detail** — `mul_comm_of_antiInvolution` (`Commutativity.lean:471`):
- **Type**: `(h_fix : ∀ D, ι.onHeckeCoset D = D) (f g : 𝕋 P ℤ) → f * g = g * f`.
- **What**: If an anti-involution `ι` of the ambient group fixes every
  double coset (i.e. `ΗδΗ = ΗδˉΗ` for every δ), then the Hecke ring is
  commutative.
- **How**: Reduces to commutativity on `T_single` generators, then to
  equality of the multiplicities `m(g₁, g₂, d) = m(g₂, g₁, d)`. The
  equality is witnessed by an explicit bijection `decompQuot g₁ →
  decompQuot g₂` (see `heckeMultiplicity_le_comm_fwdMap`, line 332) built
  from the anti-involution and the H-stabilizer manipulations encoded in
  `conj_kernel_mem_of_stabilizer_mem` and `fwd_pair_mem`.
- **Hypotheses**: An anti-involution of `G` (a contravariant group
  involution sending `H ↔ H`, `Δ ↔ Δ`), plus the fixed-points-of-cosets
  condition.
- **Uses from project** (in this file): `m_comm_of_onHeckeCoset_eq`,
  `heckeMultiplicity_comm_of_onHeckeCoset_eq`, `T_single_mul_T_single`,
  `decompQuot`, plus the entire helper `heckeMultiplicity_le_comm_fwdMap`
  chain (lines 332–434).
- **Visibility**: public.
- **Lines**: 471–484 (proof ~14 lines, but depends on ~140 lines of helpers in the same file).
- **Notes**: clean; no `sorry`, no `set_option`.

---

### Cluster B: `HeckeRIngs/GLn/` (general-n Hecke ring, 14 files + 7 BlockBijection + 6 CongruenceHecke, 850 decls)

**Module purpose.** Instantiates the abstract Hecke ring for the
`GL_n(ℤ_p)`-style Hecke pair `(G = GL_n(ℚ), H = GL_n(ℤ), Δ = M_n(ℤ) ∩ G)`,
proves that diagonal Smith-normal-form matrices give canonical double-coset
representatives, and develops the **polynomial-ring structure** of the
p-local Hecke ring (Shimura Theorem 3.20).

| File | Lines | Purpose |
|------|------:|---------|
| `Basic.lean` | 597 | `GL_pair n` (the GL_n Hecke pair); `GL_pair_Δ_def` etc. |
| `PrimeDecomposition.lean` | 1232 | Each Δ_n-element factors uniquely as a product of `ppowDiag p e`-matrices |
| `DiagonalRepresentatives.lean` | 791 | Smith-normal-form canonical reps for double cosets |
| `Degree.lean` | 1146 | `deg(T(d₁,…,d_n))` formula |
| `CoprimeMul.lean` | 1180 | Hecke multiplication respects the coprime-Smith decomposition |
| `DiagonalCosets.lean` | 1187 | Explicit left-coset count for diagonal matrices (the only 2 `set_option linter.unusedSimpArgs false` of the project, lines 794, 809) |
| `PolynomialRing.lean` | 1163 | Defines `R_p := image of evalHom`; `evalHom` is the polynomial-ring map from `MvPolynomial (Fin n) ℤ` into `𝕋 (GL_pair n) ℤ` localised at `p`. Carries 2 `sorry`s at lines 952, 963 — both labelled "general n requires Phase B/C" |
| `CosetDecomposition.lean` | 859 | Explicit (a, b, d) parameter coset enumeration |
| `Projection.lean` | 412 | Shimura Lemma 3.19 (coefficient compatibility) + dim-compat induction; carries 4 `sorry`s (lines 238, 255, 365, 409), all labelled "general n requires Phase B/C only for Thm 3.20, not Thm 3.35 at n=2" — i.e. these are *deliberately* unfilled because the project's terminal goal at `n=2` doesn't need them |
| `SL2Surjection.lean` | 622 | Builds `SL₂ ↠ GL_2-block` |
| `SLnTransvection.lean` | 1086 | SL_n transvection generation lemmas |
| `TransposeAntiInvolution.lean` | 366 | The transpose is an anti-involution; checks the `AntiInvolution` axioms |
| `BlockBijection.lean` (root) | 411 | Aggregator |
| `BlockBijection/SLReduction.lean` | 1669 | The block-diagonal SL-reduction |
| `BlockBijection/HeckeMultBridge.lean` | 1078 | Bridges block multiplicity to general multiplicity |
| `BlockBijection/BlockEmbed.lean` | 977 | Block-embedding of the smaller GL_n into the larger |
| `BlockBijection/FiberPreimageJ.lean` | 1054 | Carries 1 `sorry` at line 939: `fiber_has_block_form_preimages` (the structural input for the BlockEmbed bijection that, like the Projection.lean sorries, would be needed for the general-n induction but is unused for `n = 2`) |
| `BlockBijection/AbstractHeckePair.lean` | 524 | |
| `BlockBijection/StabFiberIBlock.lean` | 783 | |
| `BlockBijection/TrailingHNF.lean` | 591 | |
| `CongruenceHecke.lean` (root) | 173 | Aggregator |
| `CongruenceHecke/Foundation.lean` | 1019 | The Δ₀(N) congruence-Hecke pair foundation |
| `CongruenceHecke/Presentation.lean` | 1192 | Presentation by `T_p_gen`; has a sorry-via-import comment for the general-n case |
| `CongruenceHecke/Surjectivity.lean` | 1646 | T_p generation surjectivity |
| `CongruenceHecke/AtkinLehner.lean` | 925 | Atkin–Lehner involutions on congruence Hecke |
| `CongruenceHecke/Props.lean` | 720 | Property bundles |
| `CongruenceHecke/DegreeCombinatorics.lean` | 1245 | Counts cosets (DiagonalCosets-related, has 1 `_local` helper) |

**Headline (cluster B)**:
`HeckeRing.GLn.evalHom` ranges over the full p-local Hecke ring (Shimura Thm
3.20 / Miyake Thm 3.2.10); concretely, for n=2 this is the polynomial ring
`ℤ[T_p, T_{p,p}]` (combined with `n=2`-specific machinery in `GL2/`).

---

### Cluster C: `HeckeRIngs/GL2/` top-level (34 files, ~2,328 decls in subtree)

**Module purpose.** The `n=2` instance: `GL₂(ℚ)` Hecke pair, `T_p` and
`T_n` operators on `M_k(Γ₁(N))`, character decomposition by Nebentypus,
and the multiplication-table theorem (Miyake 4.5.13).

| File | Lines | Purpose |
|------|------:|---------|
| `Basic.lean` | 322 | `T_ad a d`, `T_p`, `T_(p,p)` Hecke basis elements; `T_p_unfold` etc. |
| `Degree.lean` | 437 | `deg(T_p) = p + 1` and family |
| `MultiplicationTable.lean` | 871 | `T_p^a * T_p = T_{p^(a+1)} + p T_{p,p} T_{p^(a-1)}` etc. |
| `Prop334.lean` + `_HeckeSlash.lean` + `_HeckeSlashDiag.lean` + `_StabSurj.lean` | ~1,700 total | Shimura Prop 3.34 (the slash action on Hecke double cosets) and its constituents |
| `Gamma1Pair.lean` | 583 | The `(GL₂(ℚ), Γ₁(N), Δ₁(N))` Hecke pair |
| `HeckeAction.lean` | 353 | `actHeckeCoset_M_k` — Hecke action on M_k(Γ₁(N)) |
| `HeckeActionGeneral.lean` | 547 | Generalization to arbitrary congruence subgroups |
| `HeckeModularForm.lean` + `_Gamma0.lean` | ~900 total | Hecke ring acts on M_k by ring hom |
| `HeckeT_p.lean` | 1073 | The classical T_p with explicit `T_p_upper`/`T_p_lower` coset reps; `heckeT_p_cusp` |
| `HeckeT_n.lean` | 2056 | T_n for n coprime to N, defined via `T_p`-products; `fourierCoeff_heckeT_n_period_one` (the formula `a_n(T_m f) = ∑_d d^{k-1} χ(d) a_{mn/d²}`) |
| `HeckeT_n_*.lean` (5 files, ~3,500 LOC) | | T_n on Γ_0, Γ_1, GLpair, CharSpace, with bridges; multiple commutativity proofs |
| `HeckeSlashExplicit.lean` | 522 | Explicit formula for `f ∣[k] T_n` |
| `FourierHecke.lean` | 528 | The interaction of Fourier coefficients with Hecke operators |
| `LevelEmbed.lean` | 871 | Trivial inclusion `M_k(Γ₁(M)) ↪ M_k(Γ₁(N))` for `M ∣ N` |
| `LevelRaise.lean` | 819 | `V_d : f ↦ f(d·)` raising operator; `heckeT_n_levelRaise_comm` |
| `CharacterDecomp.lean` | 687 | Decomposition by Nebentypus `χ` |
| `CharSpaceIso.lean` | 449 | `modFormCharSpace k χ ≃ ...` isomorphisms |
| `CongruenceIndex.lean` | 309 | `[Γ : Γ₁(N)]` and friends |
| `DeltaEigenform.lean` | 481 | The `Δ` discriminant as an eigenform for all `T_n` |
| `BadPrimeDoubleCoset.lean` | 1156 | The bad-prime double cosets (p ∣ N) |
| `Newforms.lean` (root, 580 LOC) | | Aggregator + `Newform.eulerStrippingArithmeticInput_of_heckeStruct` + `Newform.CompletedMellinData` |
| `Unified.lean` (root) | | Aggregator |
| `AdjointTheory.lean` (root, 910 LOC) | | Core cusp/Hecke infrastructure for the spectral theorem |
| `AdjointTheoryPetersson.lean` (1061 LOC) | | The Petersson development; `eigenforms_orthogonal_of_ne_eigenvalues`; `exists_simultaneous_eigenform_basis`; `exists_eigenform_decomposition_of_invariant` |
| `AdjointTheory/ConcreteFamily.lean` | 6,052 | The concrete `δ_b` representative system for T_p adjoint; **largest file**; contains the dead `_doubleCoset` cluster (see Junk) and the live trace-engine route `petN_heckeT_p_adjoint_via_trace` |
| `AdjointTheory/TileBridge.lean` | 4,352 | The DS double-coset tile bridge |
| `AdjointTheory/DeltaBSystem.lean` | 3,451 | The DS-standard δ_b representative system |
| `AdjointTheory/FDTransport.lean` | 2,300 | FD-transport infrastructure (`Γ_p(α)` trace engine) |
| `AdjointTheory/SummandAdjoint.lean` | 1,945 | Summand-level adjoint identity |

#### Headline-decl detail — `heckeT_p_adjoint` (`ConcreteFamily.lean:5983`):

- **Type**:
  ```
  (p hp hpN) (f g : CuspForm) →
    petN (heckeT_p_cusp k p hp hpN f) g =
    petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ (heckeT_p_cusp k p hp hpN g))
  ```
- **What**: DS Theorem 5.5.3 / Miyake Theorem 4.5.4 — the adjoint of T_p with
  respect to the level-N Petersson product `petN` is `⟨p⟩⁻¹ T_p` (the
  diamond-twisted T_p).
- **How**: One-liner — delegates to `petN_heckeT_p_adjoint_via_trace`. The
  *via-trace* route (defined just above this theorem) uses the FDTransport
  `Γ_p(α)` trace engine: rewrites `petN (T_p f) g` as an integral over the
  Γ_p(α) fundamental domain, applies the `setIntegral_Γ_p_α_fundDomain_PSL`
  trace identity, then folds back into `petN`. Critically, this route avoids
  the false per-tile DS 5.5.2(b) split.
- **Hypotheses**: p prime, coprime to N, and just two cusp forms.
- **Uses from project**: `petN_heckeT_p_adjoint_via_trace` (only),
  via that: `setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain`
  (FDTransport.lean), `traceSlash_T_p_lower_eq_diamond_inv_heckeT_p`,
  `isFundamentalDomain_Hecke_tiles_biUnion_Gamma_p_α`,
  `slToPslQuot_fiberCard_Gamma_p_α_T_p_lower_eq_fiberCard`,
  `petN_eq_setIntegral_Gamma1_fundDomain_PSL`.
- **Visibility**: public.
- **Lines**: 5983–5993 (proof: 1 line — the entire chain is in the helper).
- **Notes**: NOT in the dead `_doubleCoset` cluster (lines 5471–5519, 6015–6051).

---

### Cluster D: `HeckeRIngs/GL2/Newforms/` (10 files, ~10k LOC)

**Module purpose.** The newform / oldform decomposition `S_k(Γ₁(N)) =
S_k^old ⊕ S_k^new`; the `Newform` and `Eigenform` structures; the Main
Lemma (DS 5.7.1); Atkin–Lehner uniqueness; Fricke involution; Mellin
bridges to the L-function; Hecke multiplicativity (DS 5.8.5).

| File | Lines | Purpose |
|------|------:|---------|
| `Basic.lean` | 1218 | `Eigenform`, `Newform`, `cuspFormsOld`, `cuspFormsNew`, `oldPart`, `newPart`; the projection `(cuspFormsOld ⊕ cuspFormsNew)`-IsCompl; `cuspFormToModularFormLin` |
| `LevelRaiseComm.lean` | 1095 | `cuspFormsOldExtended` (the level-raise-images-closed version); `heckeT_n_levelRaise_comm` |
| `BadPrimeAdjoint.lean` | 1217 | The p ∣ N adjoint analysis; `cuspFormsOldExtended_disjoint_cuspFormsNewExtended`; `NewformExtended` structure |
| `BadPrimeReduction.lean` | 1560 | Reduction techniques for bad primes |
| `BadPrimeCosets.lean` | 1242 | `T_p_lower_with_offset` cosets for the p ∣ N case |
| `MainLemma.lean` | 549 | The Main Lemma `mainLemma` (line 435, **carries the project's headline `sorry`** — the char-free DS 5.7.1, still open) + `newform_unique` + `eigenvalue_eq_coeff` |
| `MellinBridges.lean` | 1654 | Bridges Newforms to Mellin transforms / L-functions; `FrickeSlashData`, `ImAxisMellinData`, `CompletedMellinData` |
| `Fricke.lean` | 1501 | `frickeMatrix`, `frickeSlashCuspForm`, the Fricke involution `W_N` |
| `FrickeTwist.lean` | 1491 | `FrickeTwistData` |
| `CoeffSeq.lean` | 1303 | `Newform.lCoeff`, `IsHeckeCoefficientSequence`, `lSeries`, prime-power coefficient formulas; **carries `sorry`** at line 1249: `exists_nonzero_prime_eigenvalue` (a charge-free version of "a newform has a nonzero eigenvalue at almost all primes") and the older `strongMultiplicityOne` (line ~1264) which is NOT used by the headline |

#### Per-decl detail — `Newform` structure (`MainLemma.lean:163`):

- **Type**: bundles a `CuspForm ((Gamma1 N).map (mapGL ℝ)) k` with `isEigen`,
  `isNorm` (= `a₁ = 1`), `isNew` (∈ `cuspFormsNewExtended`).
- **What**: A normalised newform — the central object of the project's
  headline.
- **How**: Definition only.
- **Visibility**: public structure.

#### Per-decl detail — `mainLemma` (`MainLemma.lean:435`):

- **What**: DS Theorem 5.7.1 (Atkin–Lehner): a cusp form whose coprime-to-N
  Fourier coefficients vanish lies in the oldspace.
- **How**: stub `sorry`. The docstring spells out the intended argument:
  spectral decomposition + adjoint of T_n gives `⟨f_new, g⟩ = λ_n⁻¹ ⟨T_n
  f_new, g⟩` for each new eigenform `g`, which vanishes since
  `a_n(f) = 0`. **Single intentional sorry; explicitly documented as an
  upstream-spectral input**, deliberately deferred to the route-B chain in
  `SMOObligations/`.
- **Notes**: This is **not** in the closure of
  `strongMultiplicityOne_constMul` (per the project memory kernel verification
  2026-05-27).

---

### Cluster E: `HeckeRIngs/GL2/Unified/` (14 files, ~12k LOC)

**Module purpose.** A "unified" recast of the Hecke action that fully
factors through the Nebentypus character — `χ-isotypic` everything. Hosts
`GoodHeckeRing`, `NebentypusHeckeRingHom`, `TwistedHeckeRing`,
`PrimeHeckeRing`. The architectural goal is: produce a single ring
homomorphism `R_p → End(S_k(Γ₁(N),χ))` whose image is the commutative
"good Hecke" subalgebra, so that simultaneous diagonalisation is automatic.

| File | Lines | Purpose |
|------|------:|---------|
| `Core.lean` | 537 | `GoodHeckeIndex N`, `GoodHeckeFamily` — the abstract good-family API |
| `GoodHeckeRing.lean` | 1058 | The commutative subalgebra generated by good-index operators |
| `NebentypusHeckeRingHom.lean` | 1565 | `heckeT_n_cusp_eq_heckeRingHom`; the unified ring-hom statement |
| `NebentypusSpace.lean` | 935 | `modFormCharSpace k χ` API restated |
| `Gamma1CharSpace.lean` | 728 | Γ₁ slice of the character space |
| `TwistedHeckeRing.lean` | 1398 | The twisted Γ₀(N) Hecke ring acting on Nebentypus spaces |
| `TwistedSlash.lean` | 825 | Twisted slash action |
| `PrimeHeckeRing.lean` | 875 | Prime-only ring |
| `CoprimeCommutativity.lean` | 901 | Commutativity at coprime indices |
| `CuspNebentypusSpace.lean` | 1023 | `heckeT_n_cusp_charRestrict_commute_from_mulFormula` |
| `Adjoint.lean` | 1145 | Petersson-adjoint formula in the unified language |
| `EigenformFromRing.lean` | 988 | `exists_eigenform_decomposition_of_invariant` (in the unified language) |
| `Downstream.lean` | 770 | Connection back into Newform-MainLemma |
| Other (`Unified.lean`, `Gamma1Trivial.lean`, `Gamma0Trivial.lean`) | <500 each | Aggregators + trivial cases |

---

### Cluster F: `Eigenforms/` (6 files, ~8k LOC) — **the route-B development**

**Module purpose.** A **second** (parallel) development of Atkin–Lehner /
Main Lemma material, following **Miyake's** §4.6 organisation rather than
DS. This is what `SMOObligations.lean` actually imports; it produces the
character-conditional `mainLemma_charSpace_routeB`, dodging the analytic
`sorry` in `Newforms/MainLemma.lean`.

| File | Lines | Purpose |
|------|------:|---------|
| `HeckeLemma.lean` | 1234 | Low-dependency Hecke API scaffold (T045); `IsHeckeOldOnDvdSubmodule` |
| `AtkinLehner.lean` | 1329 | Same-level p-supported projection API; `qSupportedOnDvdSubmodule`; the dichotomy `cuspFormsOld_le_iSup_qSupportedOnDvdSubmodule_divisors` |
| `AtkinLehnerProjection.lean` | 1532 | The Mobius-inversion projection `cuspFormsOld_of_coprime_coeff_vanishing_via_Mobius`. **Closes the Main Lemma at the per-character level**, sidestepping the analytic spectral input |
| `TraceOperator.lean` | 461 | Trace/descent from Γ₁(M) to Γ₁(N); the V_l-adjoint |
| `MainLemma.lean` | 2221 | Miyake Theorem 4.6.5 (coprime sieving) at the Eigenform level; the file the SMO pipeline ultimately invokes |
| `ConductorTheorem.lean` | 1458 | Miyake Theorem 4.6.4 (the Conductor Theorem dichotomy) |

---

### Cluster G: `SMOObligations/` (8 files, 271 decls)

**Module purpose.** The final assembly of the headline. Each `.lean` file
discharges a specific Miyake lemma:

| File | Lines | Purpose |
|------|------:|---------|
| `Lemma4_6_8.lean` | 998 | Miyake 4.6.8 — the per-prime decomposition `f = ∑_p f_p`, via `miyake_4_6_8_subset_helper` and `_unconditional` |
| `Lemma4_6_14.lean` | 622 | Miyake 4.6.14 |
| `Miyake465.lean`, `MiyakeDescend.lean`, `LevelCommute.lean`, `SquarefreeDecomp.lean`, `DescentCosets.lean` | various | The auxiliary descent / coset lemmas; together ~3.5k LOC |
| `StrongMultiplicityOneFull.lean` | 1484 | **THE FINAL FILE**: defines `cuspFormsOldChar` (Miyake's χ-old space), proves `cuspFormsOldChar_le_cuspFormsOld` (the easy forward inclusion), proves the hard reverse `cuspFormsOld_inf_charSpace_le_cuspFormsOldChar` (line 756, via `cuspFormsOld_le_oldNewGenSpan` → `oldNewGenSpan_le_oldNewGenCharSpan` → `oldNewGenCharSpan_inf_charSpace_le_cuspFormsOldChar`), then assembles `strongMultiplicityOne_constMul` (line 1429) |
| `SMOObligations.lean` (root) | 509 | The conditional twins `miyake_4_6_8_main_lemma_cuspForm`, `coprimeSieve_admits_squarefree_decomposition_in_charSpace`, `mainLemma_charSpace_routeB`, `newform_unique_routeB`, `eigenvalues_eq_all_coprime_of_eq_off_finite`, and `strongMultiplicityOne_axiom_clean`. **All have `_unconditional` siblings** in either this same file or `StrongMultiplicityOneFull.lean`, leading to the duplication finding |

---

### Cluster H: `Modularforms/` (53 top-level + 16 subdir files, ~19k LOC)

The analytic foundation. Notable files:

| File | Lines | Purpose |
|------|------:|---------|
| `summable_lems.lean` | 1511 | Summability infrastructure (79 decls) |
| `LFunction.lean` | 1359 | L-function definitions |
| `PeterssonLevelN.lean` | 1348 | The level-N Petersson inner product `petN` — defines `petN`, proves `petN_conj_symm`, `petN_definite`, the sesquilinearity, the fundamental-domain tiling `IsFundamentalDomain.subgroup_iUnion_out_smul`, the `FiniteTileFundamentalDomain` structure |
| `JacobiTheta.lean` | 1284 | Θ₂, Θ₃, Θ₄ |
| `FG.lean` | 1206 | The F-and-G discriminant identities. **Carries 3 `sorry`s at 1195, 1202, 1206** in `FmodG_rightLimitAt_zero`, `FG_inequality_1`, `FG_inequality_2`. These are flagged sorries for analytic content (lim_{t→0⁺} F(it)/G(it) = 18/π², plus the two pointwise inequalities) that the project hasn't yet derived |
| `Eisenstein.lean` | 1054 | E_k Eisenstein series |
| `EisensteinBase.lean` | 1030 | Base case |
| `Derivative.lean` | 972 | Serre derivative `serre_D`; **carries 1 `sorry`** at line 818 for `antiSerreDerPos` (a sign-propagation argument for the Serre derivative on the imaginary axis) |
| `PSL2Action.lean` | 754 | PSL₂(ℝ) action |
| `ThetaDerivIdentities.lean` | 752 | Θ-derivative identities |
| `DimensionFormulas.lean` | 751 | Dimension formulas for `M_k(Γ)` |
| `PeterssonInnerProduct.lean` | 710 | Pre-level-N Petersson |
| `Delta.lean` | 598 | Δ discriminant |
| `FG/` (5 files) | <600 each | FG-cluster auxiliary |
| `SummableLemmas/` (5 files) | <600 each | Summability decomposition |
| `DimGenCongLevels/` (5 files) | <600 each | Dimension at general congruence levels |
| `Matrix/SL2SmithDecomp.lean` | 250 | SL₂(ℤ) Smith decomposition |
| `ForMathlib_*` (4 files) | various | **Mis-located** mathlib-upstream candidates that sit under `Modularforms/` rather than `ForMathlib/` |

#### Per-decl detail — `petN` (`PeterssonLevelN.lean:67`):

- **Type**: `petN (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : ℂ`.
- **What**: The level-N Petersson inner product, defined as a finite sum
  over `SL₂(ℤ) / Γ₁(N)` of `peterssonInner` of the slash-pulled-back
  cusp forms over the SL₂(ℤ) fundamental domain `fd`. Equals
  `∫_{D_N} petersson k f g dμ` where `D_N = ⋃_δ δ⁻¹(D)` is a
  Γ₁(N)-fundamental domain (this is exactly the content of
  `IsFundamentalDomain.subgroup_iUnion_out_smul`, line 265).
- **How**: Definition is a finite sum (Γ₁(N) has finite index in SL₂(ℤ),
  giving the `instance : Fintype (SL(2,ℤ) ⧸ Gamma1 N)` at line 51).
- **Hypotheses**: just two cusp forms.
- **Visibility**: public, noncomputable.

---

## Part 2: Cross-File Dependencies

### Most-imported files (incoming-edge count from `^import LeanModularForms` greps)

| File | Imported by | Significance |
|------|------------:|--------------|
| `HeckeRIngs/GL2/LevelRaise.lean` | 14 | Core inclusion machinery |
| `HeckeRIngs/GL2/LevelEmbed.lean` | 14 | Core inclusion machinery |
| `Modularforms/PeterssonLevelN.lean` | 13 | Used in newforms + adjoint chain |
| `Eigenforms/ConductorTheorem.lean` | 13 | The dichotomy lemma is consumed widely |
| `Modularforms/DimensionFormulas.lean` | 12 | |
| `HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean` | 12 | |
| `HeckeRIngs/GL2/CharacterDecomp.lean` | 12 | |
| `HeckeRIngs/GL2/AdjointTheoryPetersson.lean` | 12 | |
| `Modularforms/SlashActionAuxil.lean` | 11 | |
| `Modularforms/LFunction.lean` | 11 | |

### Headline dependency closure

`SMOObligations/StrongMultiplicityOneFull.lean::strongMultiplicityOne_constMul`
transitively depends on:
- `SMOObligations.lean` (the route-B aggregator):
  `mainLemma_charSpace_routeB`,
  `coprimeSieve_admits_squarefree_decomposition_in_charSpace`,
  `miyake_4_6_8_main_lemma_cuspForm`
- `SMOObligations/Lemma4_6_8.lean::miyake_4_6_8_subset_helper`
- `Eigenforms/MainLemma.lean::cuspFormsOld_of_coprime_coeff_vanishing` (the
  Möbius projection, sorry-free)
- `Eigenforms/AtkinLehner*.lean::mainLemma_charSpace_of_sameLevelDivisorDecomposition`
- `HeckeRIngs/GL2/Newforms/Basic.lean::cuspFormsOld`, `cuspFormsNew`,
  `oldPart`, `newPart`, `cuspFormsOld_disjoint_cuspFormsNew`
- `HeckeRIngs/GL2/AdjointTheory/ConcreteFamily.lean::heckeT_p_adjoint` (the
  trace-engine route, sorry-free)
- `HeckeRIngs/GL2/AdjointTheoryPetersson.lean::eigenforms_orthogonal_of_ne_eigenvalues`
- The Petersson `petN` API in `Modularforms/PeterssonLevelN.lean`

It does **not** depend on:
- `HeckeRIngs/GL2/Newforms/MainLemma.lean::mainLemma` (the open sorry!)
- The dead `_doubleCoset` cluster in `ConcreteFamily.lean`
- The 4 `sorry`s in `GLn/Projection.lean` (general-n only)
- The sorry in `GLn/BlockBijection/FiberPreimageJ.lean`
- The sorries in `FG.lean` / `Derivative.lean` / `Prototype.lean`

(per the kernel-verified record in the project memory MEMORY.md, 2026-05-27).

---

## Part 3: Mathlib API Audit

### 3a. Definitions that are already at the right abstraction

The project is generally well-aligned with mathlib API:

- **`Filter.Tendsto`** is used directly throughout the limit work; no
  hand-rolled `∀ ε > 0, ∃ N, ...` patterns detected.
- **`ContinuousAt` / `ContinuousOn`** are used for continuity (no
  hand-rolled ε-δ found).
- **`Finset` over `Set.Finite`** is the dominant choice (only 2
  `Set.Finite` mentions across the whole project).
- **`Summable` / `HasSum`** are the chosen summability predicates.
- **`Submodule`-valued** `cuspFormsOld` / `cuspFormsNew` / `cuspFormCharSpace`
  / `cuspFormsOldChar` — all are explicit `Submodule ℂ (CuspForm …)`, so the
  full submodule API (`Submodule.span`, `Submodule.sum_mem`, `disjoint_def`,
  `iSup`, etc.) is available.
- **`Fintype (SL(2,ℤ) ⧸ Gamma1 N)`** is supplied as a real `instance` (line 51 of
  `PeterssonLevelN.lean`) rather than as an inline existential — good.

### 3b. Definitions to consider replacing with mathlib

1. **`Modularforms/IsCuspForm.lean::cuspFormOfSIFTendstoZero`** — wraps the
   "SIF + tends to zero at the cusp ⟹ cusp form" construction. Worth checking
   whether mathlib's `CuspFormClass.mk` from `IsZeroAtImInfty` is now
   sufficient; if so, this becomes a one-liner.

2. **`HeckeRIngs/AbstractHeckeRing/Basic.lean::HeckePair` and the
   `dcSetoid` / `lcSetoid`** — at the level of pure double-coset theory,
   mathlib has `QuotientGroup` infrastructure but not double cosets as a
   first-class object. **No mathlib replacement exists**; the
   project's definition is canonical (and an upstream-PR candidate, since
   double-coset Hecke rings are missing from mathlib).

3. **`Modularforms/PeterssonLevelN.lean::FiniteTileFundamentalDomain`**
   (line 1221) — a structure for "a finite-tile measurable fundamental
   domain". Mathlib has `MeasureTheory.IsFundamentalDomain`. The new
   structure adds a `Fintype ι` decomposition; consider whether it can be
   stated as a *predicate* `IsFiniteTileFundamentalDomain` on
   `IsFundamentalDomain`, with `tile`/`union` becoming derivations.

4. **The `Eigenform` structure** at `Newforms/Basic.lean:48`. Mathlib has
   `Module.End.HasEigenvalue` but not a dedicated joint-eigenform
   structure. The `eigenvalue : ℕ+ → ℂ` field could be replaced by a lookup
   that recovers the eigenvalue from the eigen equation, removing the
   need to store it. (Action: minor refactor, low priority.)

### 3c. API choice improvements

1. **Convert lambda syntax `=>` → `↦`** (per project's own arrow-style memory
   note, `feedback_arrow_style.md`). 1,221 occurrences of `fun x => ...`
   remain — mostly in older files. **Mechanical fix** (project memory
   already documents the rule: only touch lambdas, never `match` / `conv`
   / `do` arrows). See P1-API-1.

2. **Use `@[fun_prop]` more aggressively.** Only 41 `@[fun_prop]` tags
   across 185 files. Several files prove `Continuous` / `MDifferentiable`
   chains by hand where `fun_prop` would discharge them automatically.
   (Action: add `@[fun_prop]` to the continuity / differentiability
   companion lemmas in `Modularforms/Derivative.lean`,
   `JacobiTheta.lean`, the Eisenstein cluster.) **Concrete**:
   `D_MDifferentiable` etc. in `Derivative.lean` should carry `@[fun_prop]`.

3. **Increase `@[ext]` tag count.** Only **1** `@[ext]` lemma in the
   whole project! With structures like `Newform`, `Eigenform`,
   `NewformExtended`, `HeckeFEData`, `MellinPairData`, `FrickeSlashData`,
   `IsHeckeCoefficientSequence`, etc., each should have an `@[ext]` lemma
   to enable `ext` tactic. (Action: add for each public structure.)

4. **`@[simp]` companion lemmas for `petN`.** Search shows `petN_zero_left`,
   `petN_zero_right`, `petN_neg_left`, `petN_neg_right`, `petN_add_left`,
   `petN_add_right`, `petN_smul_right` exist as plain lemmas. They should
   carry `@[simp]` for automatic simplification of Petersson expressions.
   (Action: tag, low risk.)

### 3d. Hand-rolled patterns to replace

1. **Inline `let` bindings inside `simp_rw`/`rw` proofs.** Project memory
   note (`session 34`, the `finset_min_sep` heartbeat fix) records that
   `let`-bound variables inside heavy `rw`/`simp` chains cause `isDefEq`
   blow-up. A static-analysis pass for `let`-then-`rw` in proofs over 30
   lines is worthwhile.

2. **No `set_option maxHeartbeats`** in this project — but **per-decl
   `--max-heartbeats`** would still help locate hot spots. Recommend a
   profile-driven decomposition pass on `ConcreteFamily.lean`,
   `TileBridge.lean`, `DeltaBSystem.lean`, `FDTransport.lean`,
   `Eigenforms/MainLemma.lean` — each >2000 lines, presumably with
   sluggish elaboration.

3. **Manual character coercions.** The pair
   `(Newform.dirichletLift χ).toUnitHom = χ` is asserted via
   `MulChar.equivToUnitHom.apply_symm_apply χ` in multiple places
   (`SMOObligations.lean:139, 322, 343`, `StrongMultiplicityOneFull.lean:1441`).
   This should be a `@[simp]` lemma named e.g.
   `Newform.dirichletLift_toUnitHom`.

---

## Part 4: Moral Duplications

### Pairwise comparison table

| Decl A | Decl B | Same statement? | Same proof shape? | Verdict |
|--------|--------|-----------------|-------------------|---------|
| `miyake_4_6_8_main_lemma_cuspForm` (`SMOObligations.lean:47`) | `..._unconditional` (`SMOObligations.lean:88`) | A = B + `h_chi_factor` hypothesis | nearly identical, A delegates internally | **DELETE A**, keep B; A is now a corollary |
| `coprimeSieve_admits_squarefree_decomposition_in_charSpace` (`SMOObligations.lean:116`) | `..._unconditional` (line 185) | A = B + `h_chi_factor` | A delegates to A; B delegates to B | **DELETE A**, keep B |
| `mainLemma_charSpace_routeB` (`SMOObligations.lean:300`) | `..._unconditional` (line 332) | A = B + `h_chi_factor` | A invokes the conditional Lemma 4.6.8, B the unconditional | **DELETE A** |
| `newform_unique_routeB` (`SMOObligations.lean:347`) | `strongMultiplicityOne_axiom_clean_unconditional` (`StrongMultiplicityOneFull.lean:1466`) | newform_unique_routeB is the `h_chi_factor` version of the DS 5.8.2.1 conclusion | unconditional drops the chi_factor | **Move A into the deprecated/conditional file**, keep B in the headline file |
| `strongMultiplicityOne_axiom_clean` (`SMOObligations.lean:487`) | `strongMultiplicityOne_axiom_clean_unconditional` (`StrongMultiplicityOneFull.lean:1466`) | A = B + `h_chi_factor` | A invokes conditional newform_unique_routeB | **DELETE A**, keep B |
| `mainLemma` (`Newforms/MainLemma.lean:435` — SORRY) | `mainLemma_charSpace_routeB_unconditional` (`SMOObligations.lean:332`) | A is the char-free version (`∀ f`); B is the per-character version (`f ∈ cuspFormCharSpace k χ`) | A has no proof yet (sorry); B has the route-B proof | **CHARACTER-FREE A is a corollary of per-character B** via the χ-isotypic decomposition; either prove A from B-isotypic-collapse, or leave A sorry'd and use B everywhere. Currently the project does the latter. P4-DUP-2 |
| `Newform.eigenvalue_coprime_mul` (`CoeffSeq.lean:47`) | `eigenvalue_coprime_mul_of_coeff_one_ne_zero` (`StrongMultiplicityOneFull.lean:917`) | A is for a normalised `Newform`; B is for an unnormalised `Eigenform` with `coeff_one ≠ 0` | same proof shape (Hecke multiplicativity via `eigenform_coeff_multiplicative_one`) | **GENERALISE**: B subsumes A. Refactor A to delegate. |
| `newform_eigenvalue_at_prime_sq` (`SMOObligations.lean:254`) | `eigenvalue_at_prime_sq_of_coeff_one_ne_zero` (`StrongMultiplicityOneFull.lean:945`) | same — A for `Newform`, B for unnormalised `Eigenform` | same proof | **GENERALISE**: prove for `Eigenform`, derive for `Newform` |
| `exists_prime_coprime_avoiding_finset` (`SMOObligations.lean:397`) | `exists_prime_coprime_avoiding_finset_local` (`StrongMultiplicityOneFull.lean:985`) | identical (the `_local` is a verbatim re-statement) | identical proofs | **DELETE the `_local` copy**, import the public one |
| `qExpansion_one_coeff_one_smul_of_norm` (private, `Newforms/MainLemma.lean:221`) | `qExpansion_one_coeff_one_smul_local` (private, `StrongMultiplicityOneFull.lean:84`) | same statement, the `_local` is a re-export of a private lemma | identical | **Make the original public** (or `protected`), drop the local copy |
| `qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff_local` (private, `StrongMultiplicityOneFull.lean:98`) | (original lives in `Newforms/MainLemma.lean`) | re-export | identical | same fix |
| `cuspFormToModularFormLin_local` (`CharacterDecomp.lean:373`) | `cuspFormToModularFormLin` (`Newforms/Basic.lean:204`) | identical definition | identical | **DELETE the `_local` copy** |
| `oldPart_heckeT_n_cusp_comm` (`StrongMultiplicityOneFull.lean:798`) | `oldPart_diamondOpCuspHom_comm` (line 814) | both express "the projection commutes with X"; A for T_n, B for diamondOp | identical proof shape (decompose, project) | **UNIFY** as `oldPart_commute_of_preserves_each_subspace : ∀ T, T preserves cuspFormsOld → T preserves cuspFormsNew → oldPart ∘ T = T ∘ oldPart` — would handle both instantly |
| `heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_petersson_adjoint` (`BadPrimeAdjoint.lean:507`) | `heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_petersson_adjoint` (`MellinBridges.lean:1638`) | nearly identical name, similar statement | likely same proof | **MERGE** — investigate, possibly two stages of the same migration left side by side |
| `cuspFormsOld` (`Newforms/Basic.lean`) | `cuspFormsOldExtended` (`LevelRaiseComm.lean`) | A = "span of `levelInclude_cusp` of all `M ∣ N, M ≠ N` cusp spaces"; B = "B-closed under levelRaise" | distinct submodules with non-trivial relationship | NOT a duplication; keep both. The relationship `cuspFormsOld ⊆ cuspFormsOldExtended` is `cuspFormsOld_le_cuspFormsOldExtended` (`LevelRaiseComm.lean`) |
| `cuspFormsOld` | `cuspFormsOldChar N k χ m_χ` (`StrongMultiplicityOneFull.lean:249`) | both are "old space"; B is character-conductor-refined | substantively different (the chi-refinement is fine-grained; the file's Gap-#4 cluster establishes the partial relationship) | NOT a duplication; the two are bridged by `cuspFormsOld_inf_charSpace_le_cuspFormsOldChar` (line 756) |

**Aggregate finding: ~5 fully-deletable duplicate pairs in `SMOObligations/`**,
plus 3–4 unification opportunities in projection/commutativity lemmas. See
P4-DUP-1.

---

## Part 5: Generalization Opportunities

1. **`Eigenform.coeff_eq_coeff_one_mul_eigenvalue`**
   (`StrongMultiplicityOneFull.lean:120`) — currently stated for the
   weight-`k`, level-`N`, period-1 `q`-expansion of a `CuspForm
   ((Gamma1 N).map (mapGL ℝ)) k`. The proof only uses Hecke multiplicativity
   `aₙ(T_m f) = ∑ d|gcd ... a_{mn/d²}` (lemma
   `fourierCoeff_heckeT_n_period_one` in HeckeT_n.lean). **Could be stated
   for any weight-`k` cusp form on `Gamma1 N` lying in any `cuspFormCharSpace
   k χ`** — i.e. drop the `Eigenform` packaging and replace with a hypothesis
   `heckeT_n_cusp k n f = λ • f`. (Difficulty: low. Use case: would
   eliminate the `_local` re-export.)

2. **`HeckeRing.commutative_of_fixed_antiInvolution`** is currently for
   `𝕋 P ℤ` — but the proof is purely formal in the multiplicity counting
   and the ground ring `ℤ` is unused (the multiplicity is an integer, but
   the resulting ring is `ℤ`-linear). **Should be**:
   `mul_comm_of_antiInvolution : ∀ {Z : Type*} [CommSemiring Z], …, ∀ f g : 𝕋 P Z, f * g = g * f`.
   This would unlock the commutativity automatically for the `ℤ_p` /
   `ℚ` / `ℂ` variants. (Difficulty: medium — need to first generalise the
   `𝕋 P Z` ring structure beyond `ℤ`. `Module.lean` already does this for
   `Z` general; `Ring.lean` declares the ring structure only for `ℤ`. See
   `instSemiring` line 66 of `Ring.lean`.)

3. **`petN`** at `Modularforms/PeterssonLevelN.lean:67` is defined for
   cusp forms of weight `k : ℤ`, level `N` over `ℂ`. The Hermitian-form
   API generalises to any `RCLike` / inner product space; in particular,
   the slash action makes sense over `ℝ` too. **Generalising the
   ground field would let us share lemmas with mathlib's
   `BilinearForm`/`SesquilinForm` API.** (Difficulty: medium; would
   benefit downstream Petersson computations.)

4. **`HeckeCoset_deg`** is currently `ℤ`-valued. The `deg : 𝕋 P ℤ →+* ℤ`
   ring hom uses `ℤ`, but the underlying count is a natural number. **Should
   provide `HeckeCoset_natDeg : HeckeCoset P → ℕ`** and derive the
   integer version, which is closer to what mathlib expects of degree maps.
   (Difficulty: low.)

5. **`Eigenforms/AtkinLehnerProjection.lean::cuspFormsOld_of_coprime_coeff_vanishing_via_Mobius`**
   — Mobius inversion is a pure-combinatorial statement; the file is
   ~1500 LOC and probably has structure that could be lifted to mathlib's
   `Nat.ArithmeticFunction.Moebius` API (which `Eigenforms/MainLemma.lean`
   already imports). **Audit for opportunity to factor through the mathlib
   Möbius API directly.**

6. **The `IsHeckeCoefficientSequence` structure** at `CoeffSeq.lean:151` is
   parametrised by `(N k)`. The structure's predicates are purely about
   coefficient sequences (`coeff_one = 1`, multiplicative on coprimes,
   prime-power recursion). **Could be made independent of `N` and `k`** by
   parametrising over the Nebentypus character `χ : ℕ → ℂ` directly,
   matching the `DirichletCharacter` API in mathlib. (Difficulty: low to
   medium.)

---

## Part 6: API Improvements

### Missing lemmas (would simplify multiple proofs)

1. **`@[simp] lemma Newform.dirichletLift_toUnitHom`**: the identity
   `(Newform.dirichletLift χ).toUnitHom = χ`. Currently spelled out as
   `MulChar.equivToUnitHom.apply_symm_apply χ` at SMOObligations.lean:139,
   :322, :343, StrongMultiplicityOneFull.lean:1441 and likely more. **Add
   once, simp-tag, save dozens of lines.**

2. **`one_mem_strictPeriods_Gamma1_map`** — currently a `private`
   helper in `StrongMultiplicityOneFull.lean:74`; appears verbatim in
   multiple files. **Make public** in `HeckeRIngs/GL2/Newforms/Basic.lean`
   or similar central location.

3. **`oldPart_commute_of_preserves`** — a generic commutativity criterion
   for the `oldPart` projection: `T : End ℂ (CuspForm …) → T preserves
   cuspFormsOld → T preserves cuspFormsNew → oldPart ∘ T = T ∘ oldPart`.
   Would consolidate `oldPart_heckeT_n_cusp_comm` (line 798) and
   `oldPart_diamondOpCuspHom_comm` (line 814) of
   `StrongMultiplicityOneFull.lean` into instances.

4. **`@[ext]` structure lemmas** for every public structure:
   `Newform`, `Eigenform`, `NewformExtended`, `HeckePair`, `AntiInvolution`,
   `HeckeFEData`, `MellinPairData`, `IsHeckeCoefficientSequence`, etc.

5. **`@[simp] petN_smul_left`** — currently we have `petN_conj_smul_left`
   (which is the Hermitian-conjugate version); a simple `petN_smul_left :
   petN (c • f) g = conj c * petN f g` `@[simp]`-tag would make `simp`
   unfold smul-times-petN automatically.

6. **`@[simp] cuspFormsOldChar_eq_bot_of_conductor_eq`**'s premise
   `χ.conductor = N` should have a simp companion that recognises
   primitive characters.

7. **`Newform → Eigenform` coercion**: currently
   `f.toCuspForm` is used, but `f.toEigenform` exists in some places
   (`StrongMultiplicityOneFull.lean:1475`). **Add a `Coe Newform Eigenform`
   instance / `@[coe]` tag.**

### Missing instances

1. **`FunLike Eigenform`** / **`FunLike Newform`**: at present the
   forms-as-functions coercion is done through `f.toCuspForm`, which is a
   double step. A direct `FunLike` instance would simplify many proofs
   (the `show (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) = ⇑f.toCuspForm
   from rfl` boilerplate appears in dozens of places —
   `StrongMultiplicityOneFull.lean:237, 244, 372, 1387, 1419, ...`).

2. **`CuspFormClass`/`ModularFormClass` instances for `Newform.frickeSlashCuspForm`** —
   currently treated as a function; if it had the class instance,
   downstream proofs about `petN` of slashed newforms would inherit the
   bound/measurability lemmas automatically.

### API completeness gaps

1. **`petN` lacks `@[simp]` companions for many algebraic operations**
   (zero, neg, add, smul, scalar multiple are stated but not simp-tagged).

2. **`cuspFormsOld`/`cuspFormsNew` lack `_zero` and `_top` recognition
   lemmas**: e.g., for `χ` primitive of conductor `N`,
   `cuspFormsOldChar N k χ N = ⊥` is proved (line 273), but
   `cuspFormsNew N k = cuspFormCharSpace k χ` (the top case for primitive
   `χ`) is implicit.

3. **The `HeckeCoset_deg` ring hom does not have `Surjective`, `Injective`,
   or `ker` companion lemmas — it's the degree map, so its kernel is
   important (= the degree-0 part). Adding even `deg_one_eq_one`
   as `@[simp]` would help.

---

## Part 7: Junk / Removable Declarations

### P1-JUNK-1: The dead `_doubleCoset` cluster in `ConcreteFamily.lean`

The following private declarations form a complete, **unused** sub-development
in `LeanModularForms/HeckeRIngs/GL2/AdjointTheory/ConcreteFamily.lean`:

| Line | Decl | Status |
|------|------|--------|
| 5471 | `private theorem heckeT_p_aggregate_peeled_diagonal_balance` | The sole `sorry` here (line 5490); explicitly documented as "false tile-by-tile, holds only globally — the entire mathematical content of the dead route" |
| 5499 | `private theorem petN_heckeT_p_symmetric_form_doubleCoset` | depends on 5471 |
| 5519 | `private theorem petN_heckeT_p_symmetric_form` | thin wrapper around 5499 |
| 6015 | `private theorem petN_heckeT_p_RHS_aggregate_eq` | depends on 5499 |
| 6037 | `private theorem petN_heckeT_p_symmetric_form_global` | the "CORRECTED top assembler" |

**Used by**: none — `heckeT_p_adjoint` (line 5983) closes via
`petN_heckeT_p_adjoint_via_trace`. `petN_heckeT_p_symmetric_form_global` and
`_RHS_aggregate_eq` are referenced only by `FDTransport.lean:1659,1662`
inside *comments* (the `**The corrected global route**` docstring).

**Action**: **DELETE all 5 declarations and the surrounding ~600 LOC of
comments documenting the dead route**. The trace-engine route is the live
one; the dead cluster is preserved historical context that belongs in a
commit message, not in source. This removes the only live `sorry` in
`ConcreteFamily.lean`. P1.

### P1-JUNK-2: `AbstractHeckeRing/Prototype.lean`

The 272-line file `Prototype.lean` contains **9 `sorry`s** (lines 112,
167, 198, 199, 200, 207, 208, 244, 264) and is described in its module
docstring as a prototype. The live `AbstractHeckeRing.lean` aggregator
does **not** import it. The live `Basic.lean`, `Multiplication.lean`,
`Module.lean`, `Ring.lean`, `Associativity.lean`, `Commutativity.lean`,
`Degree.lean` collectively replace the prototype with sorry-free proofs.

**Action**: **DELETE `Prototype.lean`** (or move to a `_attic/` directory
if historical context is desired). P1.

### P1-JUNK-3: `*_local` duplicate copies

Documented above (Part 4, duplications):
- `qExpansion_one_coeff_one_smul_local` (`StrongMultiplicityOneFull.lean:84`)
- `qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff_local` (line 98)
- `exists_prime_coprime_avoiding_finset_local` (line 985)
- `conjAct_smul_H_eq_of_mem_local` (`CongruenceHecke/DegreeCombinatorics.lean:481`)
- `cuspFormToModularFormLin_local` + `_local_injective` (`CharacterDecomp.lean:373, 384`)
- `imAxis_scaled_locallyIntegrableOn` (`MellinBridges.lean:1351`) — verify if the `_local` here means "local in scope" rather than "duplicate"

**Action**: replace each with an `import` of the original. P1.

### P1-JUNK-4: The conditional `_axiom_clean` family

Per Part 4 / DUP-1: `strongMultiplicityOne_axiom_clean`,
`newform_unique_routeB`, `mainLemma_charSpace_routeB`,
`coprimeSieve_admits_squarefree_decomposition_in_charSpace`,
`miyake_4_6_8_main_lemma_cuspForm` — all have `_unconditional` siblings
that subsume them. **Action**: delete the conditional versions (or
mark them `@[deprecated, alias …]` for backwards compatibility). P4.

### P2-JUNK-5: Context-specific sorries

These sorries are *not* in the headline closure, but each should be
classified:

| Location | Decl | Status |
|----------|------|--------|
| `Modularforms/FG.lean:1195` | `FmodG_rightLimitAt_zero` | Open analytic content (lim F(it)/G(it) at 0⁺ = 18/π²); useful for downstream; keep but flag |
| `Modularforms/FG.lean:1202, 1206` | `FG_inequality_1`, `FG_inequality_2` | Same — flag |
| `Modularforms/Derivative.lean:818` | `antiSerreDerPos` | Sign-propagation argument on imaginary axis; downstream of FG.lean |
| `HeckeRIngs/AbstractHeckeRing/Prototype.lean:*` | 9 sorries | **JUNK** (see P1-JUNK-2) |
| `HeckeRIngs/GLn/PolynomialRing.lean:952, 963` | General-n cases in Shimura Thm 3.20 | Deliberately deferred ("Phase B/C") — keep with TODO, not used at n=2 |
| `HeckeRIngs/GLn/Projection.lean:238, 255, 365, 409` | Same general-n deferral | Keep with TODO |
| `HeckeRIngs/GLn/BlockBijection/FiberPreimageJ.lean:939` | `fiber_has_block_form_preimages` | Same general-n deferral |
| `HeckeRIngs/GL2/AdjointTheory/ConcreteFamily.lean:5490` | dead `_doubleCoset` route | **JUNK** (see P1-JUNK-1) |
| `HeckeRIngs/GL2/Newforms/MainLemma.lean:445` | `mainLemma` (char-free) | **Intentional**, documented; not in headline closure; *would* be nice to close via χ-isotypic-collapse from the route-B per-character version |
| `HeckeRIngs/GL2/Newforms/CoeffSeq.lean:1249` | `exists_nonzero_prime_eigenvalue` | Old route; not in headline closure |
| `HeckeRIngs/GL2/Newforms/CoeffSeq.lean:~1265` | `strongMultiplicityOne` (the *old* version of the headline) | **PROBABLY JUNK** — superseded by the SMOObligations route. Verify and either remove or mark deprecated. |

### Other potentially-junk declarations

1. **`Newform.frickeSlashSIFLin`** at `Fricke.lean:692` — wrapper around
   `frickeSlashSIF`. Audit whether the `Lin` (linear) variant adds value
   beyond a `simp` lemma.

2. **`Newform.PerNewformFullDirichletData_*` family** (`MellinBridges.lean:45`,
   149, 246, 301, 346) — 5 closely related defs. Look for unification
   opportunities.

3. **`Newform.ImAxisMellinData.of{FrickeSlashData, FrickeTwistData,
   SlashEq, ExponentialDecay, Data_auto, Data_withTwist, ImAxisData}`** —
   `Fricke.lean:308, 363, 390, 421` + `FrickeTwist.lean` — **7 constructor
   variants** for the same Mellin-data record. Investigate which are
   actually used.

---

## Part 8: Other observations

### Style adherence

- **`set_option maxHeartbeats` count: 0** — project policy enforced ✓
- **Lambda arrow style**: 30% `↦` vs 70% `=>` — needs mechanical sweep
  (P1-API-1 above).
- **Line packing**: per `feedback_line_packing.md`, signatures should be
  packed to ~100 chars, proof bodies one-tactic-per-line. Spot-check of
  `StrongMultiplicityOneFull.lean` and `PeterssonLevelN.lean` shows
  compliance.
- **Cleanup state**: the project is partway through a `/cleanup` cycle —
  `git status` shows ~14 files with uncommitted style changes (`Basic.lean`,
  `Degree.lean`, `Multiplication.lean` in AbstractHeckeRing;
  `CharacterDecomp`, `HeckeAction`, `HeckeModularForm`,
  `MultiplicationTable`, `Prop334_StabSurj` in GL2; `Basic`, `CoprimeMul`,
  `DiagonalCosets`, `PolynomialRing` in GLn; `DimensionFormulas` +
  `PeterssonLevelN` in Modularforms).

### File-size attention list

The 6 files >2000 LOC are candidates for `/split-file`:
- `ConcreteFamily.lean` (6052) — already partially split (TileBridge,
  DeltaBSystem, FDTransport, SummandAdjoint pulled out); finish the job
- `TileBridge.lean` (4352)
- `DeltaBSystem.lean` (3451)
- `FDTransport.lean` (2300)
- `Eigenforms/MainLemma.lean` (2221)
- `HeckeT_n.lean` (2056)

---

## Recommended Action Plan

### Priority 1: Quick wins (can do now, mechanical)

- **P1-JUNK-1**: Delete the `_doubleCoset` cluster in `ConcreteFamily.lean`
  (lines 5471–5519, 6015–6051, plus the ~600 lines of explanatory comments
  around 5378–5475). Removes 1 sorry, ~700 LOC. *Effort: medium (re-check
  no comment-references break documentation).*
- **P1-JUNK-2**: Delete `AbstractHeckeRing/Prototype.lean`. Removes 9
  sorries. *Effort: minutes — verify no imports.*
- **P1-JUNK-3**: Replace `*_local` copies with imports of the originals
  (6 declarations across 4 files). *Effort: hour.*
- **P1-API-1**: Mechanical `fun x => ... ↦` lambda sweep (1,221
  occurrences). Use the precise project policy: only `fun ... =>`
  lambdas, never `match`/`conv`/`do`. *Effort: scripted, but verify per
  file.*
- **P1-API-2**: Add `@[simp]` to the `petN_zero_*`, `petN_neg_*`,
  `petN_add_*`, `petN_smul_*` lemmas in `PeterssonLevelN.lean`. *Effort:
  minutes.*
- **P1-API-3**: Add `Newform.dirichletLift_toUnitHom` as a `@[simp]`
  lemma. *Effort: minutes.*
- **P1-STYLE-1**: Resolve the 14 uncommitted `git status` files (existing
  cleanup work).

### Priority 2: API improvements (significant impact)

- **P2-API-1**: Add `@[ext]` lemmas to every public structure
  (`Newform`, `Eigenform`, `HeckePair`, `AntiInvolution`,
  `IsHeckeCoefficientSequence`, `FrickeSlashData`, `MellinPairData`,
  `CompletedMellinData`, `CompletedFrickeData`,
  `EulerStrippingArithmeticInput`, etc. — ~12 structures).
- **P2-API-2**: `FunLike` instances for `Newform`, `Eigenform`,
  `NewformExtended`. Removes the `f.toCuspForm.toModularForm'` boilerplate
  (appears ~50+ times across the project).
- **P2-API-3**: Add the `oldPart_commute_of_preserves` generic lemma
  (Section 6 #3); refactor `oldPart_heckeT_n_cusp_comm` and
  `oldPart_diamondOpCuspHom_comm` as one-liner specialisations.
- **P2-API-4**: Add `@[fun_prop]` tags to continuity / differentiability
  companion lemmas across `Modularforms/Derivative.lean`,
  `JacobiTheta.lean`, the Eisenstein cluster.
- **P2-DUP-5**: Investigate
  `heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_petersson_adjoint`
  (`BadPrimeAdjoint.lean:507`) vs
  `heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_petersson_adjoint`
  (`MellinBridges.lean:1638`) — likely a stale duplicate.

### Priority 3: Generalizations & restructuring (requires thought)

- **P3-STRUCT-1**: Move `Modularforms/ForMathlib_Cusps.lean`,
  `Modularforms/ForMathlib_FunctionsBoundedAtInfty.lean`,
  `Modularforms/ForMathlib_SlashActions.lean`,
  `Modularforms/ForMathlib_UpperHalfPlane.lean` into
  `LeanModularForms/ForMathlib/` (matching the existing `ExitTimeExcision`
  / `CauchyPrimitive`). *Effort: hour (renames + import updates).*
- **P3-GEN-1**: Generalise `mul_comm_of_antiInvolution` (and the
  abstract Hecke ring's other ground-ring-specific lemmas) from `ℤ` to a
  general `CommSemiring Z`. *Effort: 1 day; unlocks `ℂ` / `ℚ` Hecke
  rings directly.*
- **P3-GEN-2**: Generalise `petN` to a `RCLike` ground field instead of
  `ℂ`. *Effort: medium; unlocks real-coefficient case (e.g. theta
  function-style real cusp forms).*
- **P3-SPLIT-1**: Continue the file-split work — start with
  `ConcreteFamily.lean` (post-P1-JUNK-1) at ~5,400 LOC; aim for
  <1,500 LOC per file. Same for `TileBridge.lean`, `DeltaBSystem.lean`,
  `Eigenforms/MainLemma.lean`, `HeckeT_n.lean`.

### Priority 4: Structural changes (major refactoring)

- **P4-DUP-1**: After P1-JUNK-* removes redundant routes, **delete the
  conditional twins** (5 theorems in `SMOObligations.lean` lines 47, 116,
  300, 347, 487 — each has an `_unconditional` sibling that subsumes it).
  *Effort: medium; need to chase 1–2 callers of the conditional forms.*
- **P4-DUP-2**: **Close `Newforms/MainLemma.lean::mainLemma`** (the
  remaining intentional `sorry`) by deriving it from
  `mainLemma_charSpace_routeB_unconditional` via χ-isotypic collapse. The
  collapse should be a 50-line proof. Once landed, this removes the
  project's last "headline-adjacent" sorry. *Effort: 1–3 days.*
- **P4-MERGE-1**: Merge the `Eigenforms/` and `HeckeRIngs/GL2/Newforms/`
  developments — both have a Main Lemma, both have Atkin–Lehner
  projections, both develop the old/new decomposition. Consolidate the
  shared API. *Effort: 1–2 weeks; the largest structural lift available.*
- **P4-MERGE-2**: Consolidate the `MellinPairData` / `ImAxisMellinData`
  / `CompletedMellinData` / `CompletedFrickeData` / `HeckeFEData` /
  `FrickeSlashData` / `FrickeTwistData` family in
  `MellinBridges.lean` + `Fricke.lean` + `FrickeTwist.lean`. ~5
  structures, 7 constructor variants → 1–2 structures with the variants
  as different constructors. *Effort: 1 week.*

---

## Final Pass Checklist

- [x] Every cluster appears in the inventory.
- [x] Every `sorry` site is classified (junk / intentional / context-specific).
- [x] Cross-file dependency map for the headline result.
- [x] Mathlib API audit (definitions, hand-rolled patterns, tags).
- [x] Duplication-check pairwise table.
- [x] Generalisation opportunities with literature considerations.
- [x] API improvements with concrete missing-lemma proposals.
- [x] Junk identification with action items.
- [x] Action plan with P1–P4 priorities.

**Scope caveats** (re-stating from the top):
- Per-decl prose entries were produced only for headline / sorry-bearing
  / cluster-anchor declarations. Other declarations are enumerated by name
  + line + file; their "What/How/Hypotheses/Uses/Notes" can be derived
  on demand via per-file `lean_file_outline` queries.
- The "moral duplication" pass is concrete on the SMOObligations cluster
  (where the duplication pattern is mechanical) and the dead-cluster /
  `_local` cases; a fuller cross-cluster pass across `Modularforms/` and
  `HeckeRIngs/GL2/` would likely surface 5–10 more candidates.
- The mathlib audit is biased toward the SMO / Petersson / Newform path
  (the areas read in detail). A re-pass on `Modularforms/Eisenstein*`,
  `JacobiTheta.lean`, and the `summable_lems.lean` family is recommended.
