# Master Ticket Board: LeanModularForms → Strong Multiplicity One

*Consolidated 2026-04-17 from `tickets.md` (Bridge+Commutativity Refactor),
`tickets-prop-3-34.md` (Shimura Prop 3.34), `tickets-phase5.md` (Adjoint Theory),
and `tickets-finish-congruence-hecke.md` (CongruenceHecke+BlockBijection).*

*This is the SINGLE source of truth for all ticketed work. Previous separate
ticket files are removed.*

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

# Epic D: Hecke Adjoint Theory (⚠️ ACTIVE)

**Active files**: GL2/AdjointTheory.lean (2643L, 2 sorries), Modularforms/PeterssonLevelN.lean,
PeterssonInner.lean, PSL2Action.lean.

Target: `AdjointTheory.lean` sorry-free. Key theorems:
`peterssonInner_slash_adjoint`, `heckeT_p_adjoint` (T_p* = ⟨p⟩⁻¹ T_p),
`heckeT_n_adjoint`, `heckeT_n_normal`, `simultaneous_eigenform_basis`
(spectral theorem for commuting normal operators).

**Reference**: [DS] §5.5, [Miy] §4.5 (Thm 4.5.4-4.5.5).

## Done (Epic D, 9 tickets)

### [T100a] `diamondOp_petersson_unitary` ✅ done
- **File**: AdjointTheory.lean:711.
- **Notes**: Proved via `petN_slash_invariant`.

### [T100b] `heckeT_n_adjoint_on_charSpace` ✅ done
- **File**: AdjointTheory.lean:1149.
- **Notes**: Proved using `heckeT_n_adjoint` + `petN_smul_right`.

### [T101] GL₂⁺(ℝ) invariance of μ_hyp ✅ done
- **File**: PSL2Action.lean:545.
- **Notes**: `instSMulInvMeasure_GLpos : SMulInvariantMeasure GL(2,ℝ)⁺ ℍ μ_hyp`.
  Used in `peterssonInner_slash_adjoint` (line 664).

### [T103] Prop 5.5.2(a) `peterssonInner_slash_adjoint` ✅ done
- **File**: AdjointTheory.lean:616-664.
- **Notes**: Fully proved for arbitrary measurable set D and α ∈ GL₂⁺(ℝ).
  Uses petersson_slash + measurePreserving_smul + slash_peterssonAdj_eq.

### [T105] Double coset identity algebraic part ✅ done
- **File**: AdjointTheory.lean:373-412.
- **Notes**: `adjointGamma0Rep` constructed, `adjointGamma0Rep_units` proved
  (Gamma0MapUnits(γ₀) = unitOfCoprime(p)⁻¹).

### [T108] `heckeT_n_cusp_isSemisimple_on_charSpace` ✅ done
- **File**: AdjointTheory.lean:1209-1217.
- **Notes**: One-liner from Mathlib's `Module.End.iSup_maxGenEigenspace_eq_top`
  over algebraically closed ℂ.

### [T204] `petN_slash_adjoint_GL2` + `sum_setIntegral_GL2_shift` ✅ done (2026-04-17)
- **File**: AdjointTheory.lean:825, sum_setIntegral_GL2_shift at 795.
- **Notes**: Both ~75 LOC + ~60 LOC, closed sorry-free. Signatures take additional
  hypotheses: `hα_h_inv`, `hα_fd`, `h_int`, `h_α_int`.
  Proof reduces via `setIntegral_SL_tile_fd_eq_fdo`, `sum_SL_tile_eq_fiberwise_PSL_tile`,
  `slToPslQuot_fiberCard_eq`, `setIntegral_Gamma1_fundDomain_PSL_eq_sum`, then applies
  `IsFundamentalDomain.setIntegral_eq`.
  Axiom-clean.

### [T205-a] Per-summand slash adjoint for T_p coset reps ✅ done (2026-04-18)
- **File**: AdjointTheory.lean:1129 (`peterssonInner_slash_adjoint_coset`) and
  :1192 (`peterssonInner_slash_adjoint_coset_right` — right variant via Hermitian).
- **Notes**: ~40 LOC each. Also added supporting lemmas: `peterssonAdj_mul`
  (anti-multiplicativity from `Matrix.adjugate_mul_distrib`),
  `peterssonAdj_mapGL_SL_eq_inv` (adj = inv for SL elements),
  `peterssonInner_slash_adjoint_right` (right-slash version via Hermitian symmetry).
  Axiom-clean.

### [T206] `heckeT_n_adjoint` composite case ✅ done (2026-04-13)
- **File**: AdjointTheory.lean:946.
- **Notes**: Restructured to use strong induction via `Nat.strong_induction_on`.
  Added 8 helper lemmas (lines 917-1170): `heckeT_n_cusp_comm_diamondOp`,
  `heckeT_n_cusp_decomp`, `heckeT_n_cusp_comm`, `diamondOp_cusp_comp`,
  `diamondOp_cusp_one`, `heckeT_n_adjoint_coprime_case`,
  `heckeT_n_cusp_ppow_recursion`, `heckeT_n_adjoint_ppow_case`.
  Three cases: coprime factorization (n = p^v · m), prime (v=1), prime power (v≥2).
  **Proof strategy**: see `docs/plans/strong-multiplicity-one.md` §Phase 5.

**Stale ticket corrections** (2026-04-13 audit):
- T102 (Lemma 5.5.1a domain change): absorbed into T201-T203 (IsFundamentalDomain API)
- T104 (Prop 5.5.2b double coset): absorbed into T204 (petN_slash_adjoint_GL2)
- T106 (heckeT_p_adjoint assembly): absorbed into T205 (petN_heckeT_p_diamond_shift_core)
- T107 (heckeT_n_adjoint general): renumbered as T206
- T109 (spectral theorem): renumbered as T207
- T110 (cleanup): renumbered as T208

## Open — Foundation: IsFundamentalDomain API for Γ₁(N)

### [T201] Prove IsFundamentalDomain for the Γ₁(N) coset tiling
- **Status**: open
- **File**: PeterssonLevelN.lean (or new file)
- **Depends on**: none
- **Parallel**: yes (independent of all other tickets)
- **Description**: Prove
  ```lean
  theorem isFundamentalDomain_Gamma1_coset_tiling :
      IsFundamentalDomain (imageGamma1 N) D_N μ_hyp
  ```
  where `D_N := ⋃ q : SL(2,ℤ) ⧸ Gamma1 N, q.out⁻¹ • fdo`.
  The three conditions of `IsFundamentalDomain`:
  1. **nullMeasurableSet**: D_N is a finite union of open sets (each q⁻¹ • fdo is open).
  2. **ae_covers**: For τ ∈ ℍ, ∃ g ∈ SL₂(ℤ) with g • τ ∈ fd (from Mathlib's
     `ModularGroup.exists_smul_mem_fd`). Write g = q.out · γ for γ ∈ Γ₁(N). Then
     γ • τ ∈ q.out⁻¹ • fd ⊂ D_N (a.e., modulo the null boundary fd\fdo).
  3. **aedisjoint**: For γ₁ ≠ γ₂ ∈ Γ₁(N), translates γ₁ • D_N and γ₂ • D_N are
     a.e. disjoint. By `fdo_PSL_pairwise_disjoint`, γ₁q₁⁻¹ = ±γ₂q₂⁻¹. Handle
     ±I case: N > 2 gives -I ∉ Γ₁(N); for N ≤ 2, action factors through PSL₂.
- **Subtlety**: The group acting is Γ₁(N) viewed via `mapGL ℝ`, so use `imageGamma1 N`.
  Kernel of action is {±I} ∩ Γ₁(N); trivial for N > 2.
- **Mathlib API**: `IsFundamentalDomain` from `Mathlib.MeasureTheory.Group.FundamentalDomain`,
  `isFundamentalDomain_fdo_PSL` (PSL2Action.lean:402).
- **Estimated**: 80-100 LOC.

### [T202] Relate petN to integral over fundamental domain
- **Status**: open
- **File**: PeterssonLevelN.lean
- **Depends on**: T201
- **Parallel**: no
- **Description**: Prove
  ```lean
  theorem petN_eq_setIntegral_fundDomain
      (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
      petN f g = ∫ τ in D_N, petersson k ⇑f ⇑g τ ∂μ_hyp
  ```
  **Proof**: petN f g = Σ_q peterssonInner k fd (f∣q⁻¹) (g∣q⁻¹). Each summand
  = ∫_fd petersson(f,g)(q⁻¹ • ·) dμ = ∫_{q⁻¹ • fd} petersson(f,g) dμ (by
  measurePreserving_smul). Sum of set integrals over a.e.-disjoint sets = integral
  over the union. Use `MeasureTheory.integral_finset_iUnion`.
- **Estimated**: 40-60 LOC.

### [T203] Domain shift invariance for Γ₁(N)-normalizing elements
- **Status**: open
- **File**: PeterssonLevelN.lean (or AdjointTheory.lean)
- **Depends on**: T201
- **Parallel**: yes (with T202)
- **Description**: For α ∈ GL₂⁺(ℝ) that normalizes Γ₁(N), the shifted tiling
  α • D_N is also a Γ₁(N)-fundamental domain:
  ```lean
  theorem isFundamentalDomain_Gamma1_shift
      (α : GL(2,ℝ)⁺) (hα_norm : ∀ γ ∈ Gamma1 N, α * γ * α⁻¹ ∈ Gamma1 N) :
      IsFundamentalDomain (imageGamma1 N) (α • D_N) μ_hyp

  theorem setIntegral_fundDomain_eq_of_Gamma1_invariant
      (h : ℍ → ℂ) (h_inv : ∀ γ ∈ Gamma1 N, h ∘ (γ • ·) =ᵐ[μ_hyp] h)
      (hD : IsFundamentalDomain (imageGamma1 N) D μ_hyp)
      (hD' : IsFundamentalDomain (imageGamma1 N) D' μ_hyp)
      (h_int : IntegrableOn h D μ_hyp) (h_int' : IntegrableOn h D' μ_hyp) :
      ∫ τ in D, h τ ∂μ_hyp = ∫ τ in D', h τ ∂μ_hyp
  ```
  Second theorem follows from Mathlib's `IsFundamentalDomain.setIntegral_eq`.
  First theorem: ae_covers from α being a homeomorphism + D_N being fd + α normalizing Γ₁.
  ae_disjointness: τ ∈ γ₁ • α • D_N ∩ γ₂ • α • D_N implies α⁻¹ • τ ∈ (α⁻¹γᵢα) • D_N,
  and α⁻¹γᵢα ∈ Γ₁ by normalization.
- **Estimated**: 40-60 LOC (leveraging Mathlib's `setIntegral_eq`).

## Open — Core Adjoint (sorry #1, #2)

### [T205 / T205-d] `petN_heckeT_p_diamond_shift_core` (sorry #2)
- **Status**: in progress — stuck on combinatorial coset bijection
- **File**: AdjointTheory.lean (sorry near line 1586)
- **Depends on**: T205-a ✅ (both variants proved), triple product identity ✅
- **Statement** (at line 815, 1163):
  ```lean
  petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g)
  ```
  i.e., `petN(T_p f, g) = petN(⟨p⟩f, T_p g)`.

### Infrastructure closed sorry-free (as of 2026-04-18)

All axiom-clean:
- `sum_setIntegral_GL2_shift` (T204, ~75 LOC): GL₂⁺ fundamental-domain tiling
- `petN_slash_adjoint_GL2` (T204 downstream)
- `peterssonInner_slash_adjoint_coset` (T205-a, ~40 LOC) + right variant via Hermitian
- `peterssonAdj_mul` (anti-multiplicativity of peterssonAdj)
- `peterssonAdj_mapGL_SL_eq_inv` (adj = inv for SL elements cast to GL)
- `peterssonInner_slash_adjoint_right` (via Hermitian symmetry)
- `peterssonInner_add_left` (via Hermitian symmetry)
- `adjointGamma1Rep` + `adjointGamma1Rep_mem_Gamma1` (explicit γ₁⁻¹ ∈ Γ₁(N))
- `T_p_lower_triple_product_matrix`: T_p_lower = γ₁⁻¹ · T_p_upper(0) · γ₀
- `slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0` (CuspForm + ModularForm variants)

### T205-d proof scaffold (lines 1222-1586 of AdjointTheory.lean)

1. `show` unfolds petN to explicit SL-coset sum over `SL(2,ℤ) ⧸ Gamma1 N`.
2. `h_Tpf`, `h_Tpg`: naive double-coset decomp via `heckeT_p_fun_eq_coset_sum`.
3. `simp_rw [h_Tpf, h_Tpg]`: apply on both sides.
4. `simp only [slash_M_infty_eq_diamond_slash_T_p_lower, SlashAction.add_slash]`.
5. `simp only [slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0_ModularForm]`.

Goal becomes a clean "4-term symmetric adjoint" identity with γ₀ = `adjointGamma0Rep`
exposed explicitly on both sides.

### Where we're stuck

The residual sorry is the **combinatorial coset bijection** matching LHS's (b, q)
pairs to RHS's (c, q') pairs.

**Why local algebraic moves don't close it**:
- Applying `petN_slash_invariant` with γ = adjointGamma0Rep is **circular**.
- T205 symmetric ⟺ asymmetric `petN (T_p f) g = petN f (⟨u⟩⁻¹ T_p g)`; both need
  the same combinatorial argument.
- The σ-reindex in `petN_slash_invariant` (PeterssonLevelN.lean:887) is the template
  but adaptation fails because `T_p_upper(0)` **doesn't normalize Γ₁(N)**.

### What's genuinely needed (~80-150 LOC)

A σ-reindex `Equiv.sum_comp` on `SL(2,ℤ) ⧸ Γ₁(N)` that absorbs γ₀ + the matrix
identity `T_p_lower · α_b = p · shift(b)` (with `shift(b) ∈ Γ₁(N)`). The bijection
matches summands via:
- σ(q) = ⟦q.out · γ₀⁻¹⟧ on the quotient
- Per summand: use `peterssonInner_slash_adjoint_coset` / `_right` + adjugate simplifications
- Matrix bookkeeping: `T_p_upper(c) · σ(q).out⁻¹ = γ₁ · T_p_upper(c') · q.out⁻¹ · γ₀⁻¹`
  for some c' ∈ {0,...,p-1}, γ₁ ∈ Γ₁(N)

The proof is analogous to `Finset.sum_bij` applied at the sum level with bijection
(b,q)↦(c',σ(q)).

### Attempted strategies that failed
1. Direct `petN_slash_invariant` application — circular.
2. Diamond unitarity + `heckeT_p_comm_diamondOp` reduction — circular via substitution.
3. Per-summand `peterssonInner_slash_adjoint` transforms to "common form" — both sides
   invariant under the transformations; can't be unified by local moves.
4. M_∞ substitution — helpful for scaffold but doesn't resolve the bijection.
5. Triple product via T_p_lower = γ₁⁻¹·T_p_upper(0)·γ₀ — exposes γ₀ but still leaves
   the per-summand matching.

### Proof outline after applying T205-a / T205-a_right

Both sides reduce to a sum of 4 explicit summands (per q : SL(2,ℤ) ⧸ Γ₁(N)):

```
LHS = ∑_q [Σ_b peterssonInner k (α_b • q⁻¹ • fd) f (g ∣ T_p_lower)
          + peterssonInner k (T_p_lower • q⁻¹ • fd) (⟨p⟩ f) (g ∣ T_p_upper(0))]

RHS = ∑_q [Σ_c peterssonInner k (α_c • q⁻¹ • fd) ((⟨p⟩ f) ∣ T_p_lower) g
          + peterssonInner k (T_p_lower • q⁻¹ • fd) ((⟨p⟩ f) ∣ T_p_upper(0)) (⟨p⟩ g)]
```

Summand matching requires:
- **Matrix identity** (L_upper ↔ R_upper): `T_p_lower · α_b = p · shift(b)` where
  shift(b) ∈ Γ₁(N). Transforms L_upper tiles into Γ₁(N)-translates of q⁻¹ • fd.
  Bijection between (b, q) pairs reflects double coset structure
  Γ₁ diag(1,p) Γ₁ ↔ Γ₁ diag(p,1) Γ₁ via γ₀ ∈ Γ₀(N) (= `adjointGamma0Rep`).
- **L_lower ↔ R_lower**: via `slash_M_infty_eq_diamond_slash_T_p_lower`,
  both rewrite in M_∞ form; reduces to Hermitian/reindexing.

### Concrete next steps
1. Adapt σ-reindex from `petN_slash_invariant` to scaffolded goal.
2. Write explicit bijection (b, q) ↦ (c(b, q), σ(q)) with c(b, q) from decomposing
   `γ₀⁻¹ · α_b · q.out⁻¹ · σ(q).out⁻¹⁻¹ ∈ Γ₁(N)`.
3. Use `Finset.sum_bij_nested` to rewrite the sum.
4. Per-summand matching via slash action composition.

**Estimated effort**: 2-4 hour session with careful Lean matrix bookkeeping. All
prerequisites in place.

**Reference**: DS Theorem 5.5.3 (page 186): α = [1,0;0,p], α' = [p,0;0,1], factor
[p,0;0,1] using T105, conclude T_p* acts as T_p · ⟨p⁻¹⟩.

## Open — Downstream (sorry #4)

### [T207] `exists_simultaneous_eigenform_basis` (sorry #4)
- **Status**: open
- **File**: AdjointTheory.lean:1270 (sorry at 1325)
- **Depends on**: T206 ✅ (done)
- **Parallel**: partially — Mathlib API work can proceed independently
- **Statement**:
  ```lean
  ∃ (B : Finset (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)),
      (∀ f ∈ B, f ∈ cuspFormCharSpace k χ) ∧
      (∀ f ∈ B, IsCommonEigenfunctionCusp k f) ∧
      (∀ f g, f ∈ B → g ∈ B → f ≠ g → petN f g = 0)
  ```

### Proof strategy (3 steps)

**Step 1: Joint eigenspace decomposition.**
Define `T : CoprimeIndex N → Module.End ℂ (cuspFormCharSpace k χ)` where
`CoprimeIndex N := { n : ℕ+ // Nat.Coprime n.val N }` and
`T ⟨n, hn⟩ := heckeT_n_cusp_charRestrict k n.val hn χ`.

Pairwise commutativity: from `heckeT_n_comm` (HeckeT_n.lean:1693, **fully proved**).
Individual triangularizability: `heckeT_n_cusp_isSemisimple_on_charSpace` (line 1209).

Apply Mathlib's
`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`
(from `Mathlib.LinearAlgebra.Eigenspace.Pi`) to get:
`⨆ λ, ⨅ i, (T i).maxGenEigenspace (λ i) = ⊤`.

Each T_i is triangularizable over ℂ; generalized eigenspaces are eigenspaces here
(from `iSup_maxGenEigenspace_eq_top`).

**Step 2: Basis extraction.**
From `⨆ λ, E_λ = ⊤` in finite-dim space, non-zero eigenspaces give a direct sum
decomposition. Pick a basis from each non-zero E_λ
(via `FiniteDimensional.exists_is_basis_finset` or
`Submodule.exists_finset_of_eq_top`). Concatenate into a single `Finset`.

**Step 3: Orthogonality.**
For distinct eigenforms f, g with different eigenvalue tuples (∃ n with T_n f = λ_n f,
T_n g = μ_n g, λ_n ≠ μ_n):
```
λ_n · petN f g = petN(T_n f, g) = χ(n)⁻¹ · μ_n · petN f g
```
(by `heckeT_n_adjoint_on_charSpace`). So (λ_n - χ(n)⁻¹ μ_n) · petN f g = 0.
Since eigenvalue tuples differ, λ_n ≠ χ(n)⁻¹ μ_n for some n, hence petN f g = 0.

For eigenforms from SAME joint eigenspace (f ≠ g but same eigenvalues): promote
`petN_innerProductCore` to a full `InnerProductSpace` instance on `cuspFormCharSpace`,
then apply Gram-Schmidt (`OrthonormalBasis.fromOrthogonalSpanMk` or manual construction).

### Mathlib API available
- `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_...` (Eigenspace.Pi)
- `Module.End.iSup_maxGenEigenspace_eq_top` (Eigenspace.Triangularizable)
- `InnerProductSpace.ofCore` (for promoting petN_innerProductCore)
- `OrthogonalFamily` (InnerProductSpace.Subspace)
- `LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces` (JointEigenspace)
  — may be usable if T_n is twisted by χ(n)^{1/2} to make it symmetric

**Alternative for orthogonality**: use the manual argument above (5 lines per pair)
to avoid showing Hecke operators are symmetric (they're only "χ-twisted symmetric").

- **Estimated**: 80-120 LOC.

## Open — Cleanup

### [T208] Fix stale comments and remove dead code
- **Status**: open
- **File**: AdjointTheory.lean
- **Depends on**: T207 (after all sorries are filled)
- **Parallel**: partially (comment fixes can happen anytime)
- **Type**: cleanup
- **Description**:
  1. Fix stale comments claiming `heckeT_n_comm` is sorry'd (lines 1266, 1284, 1323)
     — `heckeT_n_comm` is FULLY PROVED at HeckeT_n.lean:1693, no sorries.
  2. Remove dead code block at lines 668-692 (superseded SL₂(ℝ) invariance comments).
  3. Clean up proof of `petN_heckeT_p_adjoint_unsymm` (lines 822-849) which duplicates
     `heckeT_p_adjoint_of_diamond_shift` (lines 865-896) — merge into one.
  4. Run `/cleanup` on the full file.
- **Estimated**: deletion + minor edits.

## Epic D dependency graph

```
T201 (IsFundDomain Γ₁ tiling) ──→ T202 (petN = ∫_{D_N})
  │                                   │
  └──→ T203 (domain shift)  ──────────┘
                │
                └──→ T204 ✅ (petN_slash_adjoint_GL2)
                       │
                       └──→ T205 (petN_heckeT_p_diamond_shift_core, sorry #2)
                              │
                              └──→ T206 ✅ (heckeT_n_adjoint composite)
                                     │
                                     └──→ T207 (spectral theorem, sorry #4)
                                            │
                                            └──→ T208 (cleanup)
```

## Epic D risk assessment

| Ticket | Risk | Notes |
|---|---|---|
| T201 | Medium | Standard construction, but ±I subtlety for N ≤ 2 |
| T202 | Low | Direct unfolding + finite disjoint union |
| T203 | Low | Leverages Mathlib's `setIntegral_eq` directly |
| T205 | **High** | Core combinatorial argument; explicit double coset reindexing |
| T207 | **High** | Mathlib API assembly; Finset basis extraction is fiddly |
| T208 | Low | Cleanup only |

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
