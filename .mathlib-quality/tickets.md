# Ticket Board: Bridge + Commutativity Refactor

## Summary (updated 2026-04-17)
- Total: 17 original + 6 new post-refactor tickets = 23
- Done: 10 (R001, R002, R006, R007, T021, + P334-A, P334-B, P334-StabSurj, CharSpaceIso, CharacterDecomp)
- Superseded: 4 (R003, R004, T020, T022 — achieved via Γ₀(N)-level refactor rather than Γ₁(N) bridge)
- In progress: 0
- Open: 9 (R005, R009, T023-T026, SMO-Ph5/Ph6/Ph7)
- Blocked: 2 (T025 — Γ₁(N) AntiInvolution doesn't fix double cosets; general-χ ring hom — Quot.out dependence)

**Major pivot (2026-04-17)**: Rather than complete the Γ₁(N) abstract bridge (T020-T026),
we went through Γ₀(N) + character decomposition. This gives:
- **Full ring hom at Γ₀(N)** (`heckeRingHom_Gamma0`) — this is R003+R006 generalized
- **`modFormCharSpace k 1 ≃ M_k(Γ₀(N))`** — bridge for trivial-χ case
- **`heckeRingHomCharSpaceOne`** — ring hom for trivial-χ (via iso)
- **Character decomposition** `M_k(Γ₁(N)) = ⊕_χ modFormCharSpace k χ`
- **Prop 3.34 infrastructure** (Gamma0MapUnits preservation, stabilizer surjectivity)

See `.mathlib-quality/plan-prop-3-34.md` and `tickets-prop-3-34.md` for the Prop 3.34 subplan.

## Tickets

### [R001] Coset-independence lemma for Hecke sums
- **Status**: done
- **File**: GL2/HeckeActionGeneral.lean
- **Depends on**: none
- **Description**: Prove that for H-invariant f, the sum `Σ f|g_i` is the same
  for any two complete sets of left H-coset reps of HδH. Specifically:
  if {g₁,...,g_n} are elements of HδH with `g_i ∈ distinct left H-cosets` and
  `n = |decompQuot|`, then `Σ f|g_i = heckeSlash_gen P k D f`.
  This is the well-definedness of the Hecke operator under different rep choices.
- **Key theorems** (all axiom-clean `[propext, Classical.choice, Quot.sound]`):
  - `slash_tRep_gen_of_mem` -- slashing by adj(h₁·δ·h₂) = slashing by tRep_gen ⟦h₁⟧
  - `heckeSlash_gen_slash_invariant` -- Hecke slash preserves H-invariance
  - `heckeSlash_gen_comp` -- composition = Hecke algebra multiplication
  - `heckeSlash_gen_comm` -- commutativity from commutative Hecke algebra

### [R002] Fill tRep_gen_D_p_matches_T_p_reps using R001
- **Status**: done
- **File**: GL2/HeckeT_p_GLpair.lean
- **Depends on**: R001
- **Description**: The T_p_upper(b) and T_p_lower are left H-coset reps for D_p
  (proved in T_p_upper_mem_D_p, T_p_lower_mem_D_p). They're in distinct cosets
  (different orbits under SL₂(ℤ)). There are p+1 of them = |decompQuot|.
  Apply R001 to get the sum equality.
- **Key theorems** (all axiom-clean `[propext, Classical.choice, Quot.sound]`):
  - `tRep_gen_D_p_matches_T_p_reps` -- abstract sum = explicit T_p sum
  - `heckeT_p_fun_eq_heckeSlash_gen` -- heckeT_p_fun = heckeSlash_gen for SL₂-inv f
  - `heckeT_p_fun_comm_of_GL_pair` -- T_p T_q = T_q T_p for SL₂-invariant f
  - `heckeT_p_comm` -- clean version using heckeT_p linear map

### [R003] Bridge heckeT_n to heckeSlashExt_gen
- **Status**: SUPERSEDED (2026-04-17)
- **Superseded by**: `heckeRingHom_Gamma0 N k` in `HeckeModularForm_Gamma0.lean` (391L)
  and `heckeRingHomCharSpaceOne` in `HeckeT_p_CharSpace_Comm.lean` (281L).
  These give ring homs at Γ₀(N) and trivial-χ levels respectively, which is
  what R003 was building toward (via a different route).
- **Note**: A similar ring hom at **general χ** remains blocked (see "general-χ
  ring hom" ticket below).

### [R004] Replace heckeT_n_comm proof with abstract version
- **Status**: BLOCKED (2026-04-17) — would create circular dependency
- **Blocker analysis** (in `HeckeT_p_CharSpace_Comm.lean` and
  `HeckeRingHomCharSpace_General.lean`): our session built
  `heckeT_p_all_charRestrict_commute_distinct` as a corollary OF the existing
  `heckeT_p_all_comm_distinct`. Using it to refactor `heckeT_p_all_comm_distinct`
  would be circular. Breaking the cycle requires a direct per-χ commutativity proof,
  which needs the general-χ ring hom — currently blocked by `Quot.out` dependence
  in `heckeSlash_gen` (see Prop334_HeckeSlashDiag.lean blocker comments).
- **Partial achievement**: the trivial-χ case IS done non-circularly via
  `heckeRingHomCharSpaceOne` and `Gamma0_pair_HeckeAlgebra_mul_comm`.

### [R005] Verify build + cleanup
- **Status**: open
- **File**: all GL2/ files
- **Depends on**: R004
- **Type**: cleanup
- **Description**: Full `lake build`, verify no regressions, check sorry count.

### [R006] Step 6: RingHom `heckeRingHom k`
- **Status**: DONE (2026-04-17) — **upgraded from AddMonoidHom to full RingHom**
- **File**: GL2/HeckeModularForm.lean (562L total, +209 this session)
- **Depends on**: none
- **Description**: `heckeRingHom k : 𝕋 (GL_pair 2) ℤ →+* Module.End ℂ (ModularForm 𝒮ℒ k)`.
  Full RingHom (not just AddMonoidHom). Uses `heckeOperator_comp` + `mul_comm` from
  the transpose anti-involution.
- **Key declarations**:
  - `heckeSum k T : Module.End ℂ (ModularForm 𝒮ℒ k)` — underlying function
  - `heckeSum_zero`, `_T_single`, `_add`, `_one`, `_mul`
  - `heckeOperator_one` + `heckeOperatorLinear_one` (identity-coset acts as identity)
  - `heckeSum_apply_apply` — bridge to heckeSlashExt at function level
  - `heckeRingHom k : 𝕋 (GL_pair 2) ℤ →+* End ℂ (ModularForm 𝒮ℒ k)` ✅
  - `heckeRingHom_apply`, `heckeRingHom_T_single` — simp lemmas
- **Extensions added this session**:
  - `heckeRingHom_Gamma0 N k` @ HeckeModularForm_Gamma0.lean (391L) — Γ₀(N) level
  - `heckeRingHomCharSpaceOne N k` @ HeckeT_p_CharSpace_Comm.lean (281L) — trivial-χ

### [R007] Step 5 setup at Γ₁(N): D_p, σ_p, M_∞, diamond identity
- **Status**: done
- **File**: GL2/HeckeT_p_Gamma1.lean (NEW, 430 lines)
- **Depends on**: R001
- **Description**: Bridge between explicit `T_p` formula at level `N` and abstract
  `heckeSlash_gen (Gamma1_pair N)`. Constructs all `p+1` coset reps and proves the
  diamond identity tying them to the explicit `T_p` formula.
- **Key declarations** (axiom-clean):
  - `D_p_Gamma1 N p hp : HeckeCoset (Gamma1_pair N)` — the double coset
  - `T_p_upper_mem_Delta1`, `T_p_upper_mem_D_p_Gamma1`
  - `aInvOfCoprime`, `mIdxOfCoprime` — explicit Bezout-style construction
  - `sigma_p_specific N p hp hpN : SL(2,ℤ)` — Γ₀(N) elt with lower-right entry
    *exactly* `p` (so factorization is clean)
  - `sigma_p_specific_mem_Gamma0`, `Gamma0MapUnits_sigma_p_specific`
  - `M_infty N p hp hpN : GL (Fin 2) ℚ` — defined directly via `mkOfDetNeZero` so
    `M_infty_val` is definitional
  - `M_infty_mem_D_p_Gamma1`
  - `M_infty_eq_sigma_mul_T_p_lower`
  - `slash_M_infty_eq_diamond_slash_T_p_lower` — **the key diamond identity**:
    `f ∣[k] M_∞ = (⟨p⟩ f) ∣[k] T_p_lower` for any modular form `f`
  - `Gamma1_pair_H_entry_is_int` — utility
  - `adj_upper_inv_mul_upper_not_mem_Gamma1` — distinctness of `p` upper coset reps

### [R008] Γ₁(N) Step 5: cardinality, bridge theorem
- **Status**: SUPERSEDED (2026-04-17) — pivoted to Γ₀(N) route
- **Rationale**: Original R008 required extending the `adj`-based bridge to Γ₁(N),
  blocked by the fact that `adj(T_p_upper(b)) = [[p, -b], [0, 1]]` has top-left `p`,
  but Γ₁(N)·diag(1,p)·Γ₁(N) requires top-left ≡ 1 (mod N).
- **Alternative taken**: Work with Γ₀(N) Hecke pair, then use character decomposition
  + iso `modFormCharSpace k 1 ≃ M_k(Γ₀(N))` to lift to Γ₁(N)-forms of trivial char.
  For non-trivial χ, ring-hom approach is blocked (see below).
- **Achieved pieces**:
  - `D_p_Gamma0 N p hp`, `T_p_coset_reps_Gamma0_equiv` (Fin(p+1) ≃ decompQuot)
  - `heckeT_p_fun_eq_heckeSlash_gen_Gamma0_on_charSpace_one` (trivial-χ bridge)

### [R009] R003+R004 vs R008 path
- **Status**: RESOLVED (2026-04-17)
- **Resolution**: Went with the Γ₀(N) + character-decomposition route instead of
  building Γ₁(N) abstract bridge from scratch. R003 is superseded by
  `heckeRingHom_Gamma0`; R004 is blocked (circular for general χ). T020-T026
  largely superseded.

---

## Phase: Cardinality + Bridge at Γ₁(N) (T020-T026)

### [T020] Lower bound: Fin(p+1) ↪ decompQuot D_p_Gamma0 (pivoted from Γ₁(N))
- **Status**: DONE (2026-04-17) — via pivot to Γ₀(N) level
- **File**: GL2/HeckeT_p_Gamma0.lean (681L)
- **Key declaration**: `T_p_coset_reps_Gamma0_equiv N p hp hpN : Fin (p+1) ≃
  decompQuot (Gamma0_pair N) (rep D_p_Gamma0)` — full Equiv, not just injection
- **Approach used**: adj-based bijection at Γ₀(N) level (where it WORKS because
  `adj(diag(1,p)) = diag(p,1) = T_p_lower ∈ D_p_Gamma0` via Bezout factorization).
  At Γ₀(N) the top-left `≡ 1 (mod N)` condition is automatic since we only need
  lower-left ≡ 0 (mod N).
- **Historical blocker** (for Γ₁(N) specifically): `adj(T_p_upper(b)) = [[p, -b], [0, 1]]`
  has top-left p, not ≡ 1 (mod N). That blocker remains for the Γ₁(N) version
  but we no longer need it.

### [T021] Conjugation preservation lemma (gcd-using) — DONE (2026-04-17) — generalized to Shimura Prop 3.34
- **Status**: DONE — delivered as `Gamma0MapUnits_preserved_of_detCoprime` @ `Prop334.lean` (373L)
- **Stronger form**: instead of just Γ₁(N)-vs-GL_pair 2, we proved Shimura's
  Proposition 3.34: for any `g ∈ Δ₀(N)` with `gcd(det g, N) = 1` and any
  `h ∈ Γ₀(N)` whose conjugate `g⁻¹ h g` lies in `Γ₀(N).H`:
  `Gamma0MapUnits(g⁻¹ h g) = Gamma0MapUnits(h)`.
- **Helpers**: matrix conjugation identity `matrix_fin_two_conj_entry_11_mod_eq`
  @ Prop334.lean — `(g⁻¹ h g)₁₁ · det g ≡ a·d·δ (mod N)`.
- **Original (weaker) approach**: Lemma:
  ```lean
  lemma conj_diag_mem_Gamma1_of_mem_GL_pair (N p : ℕ) [NeZero N] (hp : 0 < p)
      (hpN : Nat.Coprime p N) (γ : GL (Fin 2) ℚ) (hγ : γ ∈ (Gamma1_pair N).H)
      (hconj : ((diagMat 2 ![1, p]))⁻¹ * γ * (diagMat 2 ![1, p]) ∈ (GL_pair 2).H) :
      ((diagMat 2 ![1, p]))⁻¹ * γ * (diagMat 2 ![1, p]) ∈ (Gamma1_pair N).H
  ```
  Proof: extract `s ∈ Γ₁(N)` such that `γ = mapGL ℚ s`. Extract `t ∈ SL(2,ℤ)`
  for the conjugate. Show `t.val 0 0 = s.val 0 0`, `t.val 1 0 = s.val 1 0 / p`,
  `t.val 1 1 = s.val 1 1`. Show `t ∈ Γ₁(N)` via three congruences:
  - `t 0 0 ≡ 1 mod N`: `s 0 0 ≡ 1 mod N` ✓
  - `t 1 1 ≡ 1 mod N`: `s 1 1 ≡ 1 mod N` ✓
  - `t 1 0 ≡ 0 mod N`: `s 1 0 / p ≡ 0 mod N` from `s 1 0 ≡ 0 mod N` (Γ₁) +
    `p | s 1 0` (integer entries) + `gcd(p, N) = 1` ⟹ `s 1 0 ≡ 0 mod Np` ⟹
    `s 1 0 / p ≡ 0 mod N`.
- **API**: This is the lemma itself.
- **Mathlib check**: Specific to our setting; no mathlib equivalent.
- **Estimated lines**: 40–60

### [T022] Natural map decompQuot Γ₁(N) → decompQuot SL₂(ℤ)
- **Status**: open
- **File**: GL2/HeckeT_p_Gamma1.lean
- **Depends on**: T021
- **Approach**: Use `Quotient.map'` with `Gamma1_pair_H_le_GL_pair_H` for the
  underlying function. Show the equivalence relation is preserved (well-defined):
  this is automatic from the inclusion (Stab_Γ₁ ⊆ Stab_GLpair).
  Show injective: if `γ_1, γ_2 ∈ Γ₁(N).H` and `[γ_1] = [γ_2]` in level-1
  decompQuot, then `γ_1⁻¹ γ_2 ∈ Stab_GLpair = (ConjAct g • SL₂.image) ∩ SL₂.image`,
  i.e., `g⁻¹ (γ_1⁻¹ γ_2) g ∈ SL₂.image`. By T021 (since `γ_1⁻¹ γ_2 ∈ Γ₁(N).H`),
  `g⁻¹ (γ_1⁻¹ γ_2) g ∈ Γ₁(N).H`, so `γ_1⁻¹ γ_2 ∈ Stab_Γ₁`, i.e., `[γ_1] = [γ_2]`
  at level N. **Subtlety**: `decompQuot` uses `HeckeCoset.rep`, which may differ
  between levels. Either (a) prove `card_decompQuot_invariant_under_rep_change`
  helper, or (b) work with `decompQuot P diag_1p_delta` directly and show it
  has the same cardinality as `decompQuot P (rep D)`.
- **API**:
  - `decompQuot_Gamma1_to_GLpair_inj` (the natural injection)
- **Mathlib check**: `Quotient.map'`, `Subgroup.subgroupOf` exist.
- **Estimated lines**: 60–80

### [T023] Cardinality `|decompQuot D_p_Gamma1| = p + 1`
- **Status**: open
- **File**: GL2/HeckeT_p_Gamma1.lean
- **Depends on**: T020, T022
- **Approach**: From T020: `p + 1 ≤ card`. From T022 (+ level-1 `card_decompQuot_D_p`):
  `card ≤ p + 1`. Conclude `=`.
- **API**:
  - `card_decompQuot_D_p_Gamma1 : Fintype.card (decompQuot ...) = p + 1`
- **Estimated lines**: 10–20

### [CLEANUP-2] Clean HeckeT_p_Gamma1.lean after T023
- **Status**: open
- **File**: HeckeT_p_Gamma1.lean
- **Depends on**: T023
- **Type**: cleanup
- **Description**: Run /cleanup. Audit naming, generality, simp tags. Check
  no leftover sorries, no unused declarations.

### [T024] Bridge theorem `tRep_gen_D_p_Gamma1_matches_T_p_reps`
- **Status**: open
- **File**: GL2/HeckeT_p_Gamma1.lean
- **Depends on**: T023, distinctness lemmas, diamond identity
- **Approach**: Mirror `tRep_gen_D_p_matches_T_p_reps` (HeckeT_p_GLpair.lean line 557).
  Use bijection from cardinality + distinctness. The diamond identity transports
  `(⟨p⟩ f) ∣ T_p_lower` to `f ∣ M_∞`.
- **API**:
  - `tRep_gen_D_p_Gamma1_matches_T_p_reps` — abstract sum = explicit T_p sum
  - `heckeT_p_fun_eq_heckeSlash_gen_Gamma1` — bridge theorem at modular form level
- **Estimated lines**: 100–150

### [T025] CommRing for `𝕋 (Gamma1_pair N) ℤ`
- **Status**: BLOCKED (2026-04-17) — mathematically non-trivial
- **Blocker**: `onHeckeCoset D = D` (required for `instCommRing_of_antiInvolution`)
  fails at Γ₁(N) under the obvious anti-involutions. Adj sends `D(1,p) ↦ D(p,1)`
  which is a DIFFERENT Γ₁(N)-double coset for p ≢ 1 (mod N). Atkin-Lehner
  `g ↦ wN · gᵀ · wN⁻¹` doesn't preserve Δ₁(N) integrality for general g.
- **Workaround delivered**: Use `CommRing (𝕋 (Gamma0_pair N) ℤ)` (which does exist
  via `Gamma0_antiInvolution`) and bridge to Γ₁(N) via char decomposition.
  See `HeckeRingHomCharSpace_General.lean` and `Prop334*` files.

### [T026] Final commutativity payoff
- **Status**: open
- **File**: GL2/HeckeT_p_Gamma1.lean
- **Depends on**: T024, T025
- **Approach**: 5-line proof:
  ```lean
  theorem heckeT_p_all_comm_via_abstract ... := by
    rw [heckeT_p_fun_eq_heckeSlash_gen_Gamma1,
        heckeT_p_fun_eq_heckeSlash_gen_Gamma1]
    exact heckeSlash_gen_comm_commRing ...
  ```
- **API**:
  - `heckeT_p_fun_comm_via_Gamma1` — commutativity for general modular forms at level N
  - `heckeT_p_comm_via_Gamma1` — clean version using heckeT_p linear map
- **Estimated lines**: 10–20

### [CLEANUP-3] Final cleanup
- **Status**: open
- **File**: all touched files
- **Depends on**: T026
- **Type**: cleanup
- **Description**: Run /cleanup on HeckeT_p_Gamma1.lean and any modified files.
  Verify `lake build`, no sorries, axiom check.

---

## Phase: Post-refactor tickets (2026-04-17)

### [POST-1] General-χ ring hom `𝕋 (Gamma0_pair N) →+* End(modFormCharSpace k χ)`
- **Status**: BLOCKED (structural) — Quot.out dependence
- **File**: GL2/Prop334_HeckeSlash.lean, GL2/HeckeSlashExplicit.lean (scaffolding exists)
- **Depends on**: Prop 3.34 chain
- **Blocker diagnosis** (documented in Prop334_HeckeSlashDiag.lean comments):
  `heckeSlash_gen D f` uses `Classical.choice`-chosen reps. For `f ∈ modFormCharSpace k χ`
  with χ ≠ 1, changing σ.out picks up χ-factors depending on arbitrary choices.
  The sum `Σ_σ f ∣ tRep_gen σ` does not equal `heckeT_p_fun f` in general.
- **Resolution paths**:
  - (a) Char-aware matching theorem using M_∞ instead of T_p_lower as p+1-th rep
  - (b) Redefine `heckeSlash_gen` for D_p_Gamma0 to use explicit reps (Shimura/DS style)
  - (c) Accept the current state — commutativity already at heckeT_p_all level via
       existing manual `heckeT_p_all_comm_distinct`
- **Estimated lines** (if pursued): 400+ via path (a) or (b).

### [POST-2] Final refactor of `heckeT_p_all_comm_distinct` (HeckeT_n.lean:1071)
- **Status**: BLOCKED on POST-1
- **Description**: Replace 200-line manual proof with a short one via char decomp
  + per-χ ring hom. Would delete several helper lemmas (heckeT_p_all_comm_heckeT_ppow,
  heckeT_ppow_comm_same, etc.) mentioned in R004.
- **Estimated lines deleted**: ~1000 in HeckeT_n.lean if POST-1 unblocks.

### [POST-3] Phase 7: L-function infrastructure (UNBLOCKED by Phase 3 completion)
- **Status**: open, high-priority (independent of POST-1)
- **File**: new `GL2/LFunction.lean` or `Eigenforms/LFunction.lean`
- **Depends on**: none (Phase 3 is complete)
- **Description**: Define `L(s, f) = Σ a_n n^{-s}`; prove convergence for cusp forms;
  prove Euler product ⟺ normalized eigenform. See `docs/plans/strong-multiplicity-one.md`
  §Phase 7.
- **Reference**: [DS] §5.9, [Miy] Thm 4.5.16
- **Estimated lines**: ~500

### [POST-4] Phase 6 closure: fill Newforms.lean sorry #1 (L1523)
- **Status**: BLOCKED on AdjointTheory.lean (other worker's ticket)
- **File**: GL2/Newforms.lean:1523
- **Depends on**: `heckeT_n_adjoint`, `exists_simultaneous_eigenform_basis` (Phase 5)
- **Description**: Once adjoint theory completes, this sorry in the new-subspace
  forcing-zero argument closes as a short corollary.

### [POST-5] Phase 6 closure: fill Newforms.lean sorry #2 (L1654)
- **Status**: BLOCKED on L-function theory (POST-3)
- **File**: GL2/Newforms.lean:1654
- **Depends on**: Phase 7
- **Description**: `Newform.exists_nonzero_prime_eigenvalue` — needs the
  Euler product argument at bad primes to exclude vanishing.

### [POST-6] Phase 8: Miyake Main Lemma (Thm 4.6.8)
- **Status**: open
- **Depends on**: Phase 6 complete (POST-4, POST-5) or at least most of it
- **File**: new `Eigenforms/MainLemma.lean` or add to Newforms.lean
- **Description**: If `f ∈ G_k(N, χ)` and `a_n = 0` for all `n` prime to `l`, then
  either `f = 0` (good-coprime case) or `f = Σ f_p(pz)` for `p | (l, N/m_χ)`.
  See `docs/plans/strong-multiplicity-one.md` §Phase 8.
- **Estimated lines**: ~1000

### [POST-7] Phase 9: Strong Multiplicity One (Miyake Thm 4.6.12)
- **Status**: open, FINAL GOAL
- **Depends on**: POST-4, POST-5, POST-6
- **File**: new `Eigenforms/StrongMultiplicityOne.lean`
- **Description**: Short proof (~400 LOC) once Phases 6 and 8 are in place.
  See `docs/plans/strong-multiplicity-one.md` §Phase 9 for the proof sketch.
