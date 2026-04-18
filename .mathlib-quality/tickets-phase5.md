# Ticket Board: Phase 5 — Hecke Adjoint Theory

## Summary
- Total: 15 tickets (7 done + 8 open)
- Sorries remaining: 3 (lines 777, 815, 1667)
- Critical path: T201 → T202 → T203 → T204 → T205 → T207
- Parallel capacity: T201 is independent; T207 partially parallel with T205

## Audit (2026-04-13): Completed tickets

### [T100a] diamondOp_petersson_unitary ✅
- **Status**: done
- **File**: AdjointTheory.lean:711
- **Notes**: Proved via `petN_slash_invariant`.

### [T100b] heckeT_n_adjoint_on_charSpace ✅
- **Status**: done
- **File**: AdjointTheory.lean:1149
- **Notes**: Proved using `heckeT_n_adjoint` + `petN_smul_right`.

### [T101] GL₂⁺(ℝ) invariance of μ_hyp ✅
- **Status**: done (was marked open — **stale**)
- **File**: PSL2Action.lean:545
- **Notes**: `instSMulInvMeasure_GLpos : SMulInvariantMeasure GL(2,ℝ)⁺ ℍ μ_hyp`.
  Already proved sorry-free. Used in `peterssonInner_slash_adjoint` (line 664).

### [T103] Prop 5.5.2(a): peterssonInner_slash_adjoint ✅
- **Status**: done (was marked open — **stale**)
- **File**: AdjointTheory.lean:616-664
- **Notes**: Fully proved for arbitrary measurable set D and α ∈ GL₂⁺(ℝ).
  Uses petersson_slash + measurePreserving_smul + slash_peterssonAdj_eq.

### [T105] Double coset identity algebraic part ✅
- **Status**: done (was marked open — **stale**)
- **File**: AdjointTheory.lean:373-412
- **Notes**: `adjointGamma0Rep` constructed, `adjointGamma0Rep_units` proved
  (Gamma0MapUnits(γ₀) = unitOfCoprime(p)⁻¹).

### [T108] heckeT_n_cusp_isSemisimple_on_charSpace ✅
- **Status**: done (was marked open — **stale**)
- **File**: AdjointTheory.lean:1209-1217
- **Notes**: One-liner from Mathlib's `Module.End.iSup_maxGenEigenspace_eq_top`
  over algebraically closed ℂ.

## Stale ticket corrections

- **T102 (Lemma 5.5.1a domain change)**: Absorbed into T201-T203 (IsFundamentalDomain API)
- **T104 (Prop 5.5.2b double coset)**: Absorbed into T204 (petN_slash_adjoint_GL2)
- **T106 (heckeT_p_adjoint assembly)**: Absorbed into T205 (petN_heckeT_p_diamond_shift_core)
- **T107 (heckeT_n_adjoint general)**: Renumbered as T206
- **T109 (spectral theorem)**: Renumbered as T207
- **T110 (cleanup)**: Renumbered as T208

**CRITICAL correction**: Comments in AdjointTheory.lean (lines 1266, 1284, 1323)
claim `heckeT_n_comm` is "sorry'd in HeckeT_n.lean". This is **FALSE** —
`heckeT_n_comm` is fully proved at HeckeT_n.lean:1693 with no sorries.
These comments must be updated during cleanup (T208).

---

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

  1. **nullMeasurableSet**: D_N is a finite union of open sets (each q⁻¹ • fdo is open),
     hence measurable.
  2. **ae_covers**: For τ ∈ ℍ, ∃ g ∈ SL₂(ℤ) with g • τ ∈ fd (from Mathlib's
     `ModularGroup.exists_smul_mem_fd`). Write g = q.out · γ for γ ∈ Γ₁(N). Then
     γ • τ ∈ q.out⁻¹ • fd ⊂ D_N (a.e., modulo the boundary fd\fdo which is null).
  3. **aedisjoint**: For γ₁ ≠ γ₂ ∈ Γ₁(N), the translates γ₁ • D_N and γ₂ • D_N are
     a.e. disjoint. Proof: if τ ∈ γ₁ • q₁⁻¹ • fdo ∩ γ₂ • q₂⁻¹ • fdo, then
     by `fdo_PSL_pairwise_disjoint`, γ₁q₁⁻¹ = ±γ₂q₂⁻¹ in SL₂(ℤ). This forces
     q₁ = q₂ (same coset) and γ₁ = ±γ₂. Handle the ±I case by N > 2 (where -I ∉ Γ₁).
     For N ≤ 2, the action factors through PSL₂.

  **Subtlety**: The group acting must be Γ₁(N) viewed as acting on ℍ. Since the action
  factors through GL₂(ℝ)⁺ via `mapGL ℝ`, we need `imageGamma1 N` as the image subgroup.
  The kernel of the action is {±I} ∩ Γ₁(N); for N > 2 this is trivial.

- **Mathlib API**: `IsFundamentalDomain` from `Mathlib.MeasureTheory.Group.FundamentalDomain`
  (imported in PSL2Action.lean). Uses `isFundamentalDomain_fdo_PSL` (PSL2Action.lean:402).
- **Estimated**: ~80-100 lines

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
  **Proof**: petN f g = Σ_q peterssonInner k fd (f∣q⁻¹) (g∣q⁻¹). By petersson_slash_SL:
  each summand = ∫_fd petersson(f,g)(q⁻¹ • ·) dμ = ∫_{q⁻¹ • fd} petersson(f,g) dμ (by
  measurePreserving_smul). The sum of set integrals over a.e.-disjoint sets = integral
  over the union = ∫_{D_N} petersson(f,g) dμ. Use `MeasureTheory.integral_finset_iUnion`
  for the finite disjoint union.
- **Estimated**: ~40-60 lines

### [T203] Domain shift invariance for Γ₁(N)-normalizing elements
- **Status**: open
- **File**: PeterssonLevelN.lean (or AdjointTheory.lean)
- **Depends on**: T201
- **Parallel**: yes (parallel with T202)
- **Description**: Prove that for α ∈ GL₂⁺(ℝ) that normalizes Γ₁(N), the shifted
  tiling α • D_N is also a Γ₁(N)-fundamental domain, hence integrals agree:
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
  The second theorem follows directly from Mathlib's `IsFundamentalDomain.setIntegral_eq`
  (Mathlib.MeasureTheory.Group.FundamentalDomain, line 411).

  The first theorem: ae_covers follows from α being a homeomorphism + D_N being a fund
  domain + α normalizing Γ₁. ae_disjointness: if τ ∈ γ₁ • α • D_N ∩ γ₂ • α • D_N,
  then α⁻¹ • τ ∈ (α⁻¹γ₁α) • D_N ∩ (α⁻¹γ₂α) • D_N, and α⁻¹γᵢα ∈ Γ₁ by normalization,
  so disjointness follows from D_N being a Γ₁-fund domain.
- **Estimated**: ~40-60 lines (leveraging Mathlib's `setIntegral_eq`)

---

## Open — Core Adjoint (sorry #1, #2)

### [T204] petN_slash_adjoint_GL2 + sum_setIntegral_GL2_shift ✅
- **Status**: done (2026-04-17)
- **File**: AdjointTheory.lean:825, sum_setIntegral_GL2_shift at 795
- **Notes**: Both `sum_setIntegral_GL2_shift` (~75 LOC) and `petN_slash_adjoint_GL2`
  closed sorry-free. The signature of each now takes additional hypotheses:
  - `hα_h_inv`: h∘α is Γ₁(N)-invariant
  - `hα_fd`: α•D_N^PSL is a Γ₁(N)-fundamental domain
  - `h_int`, `h_α_int`: integrability on fundamental domain
  Proof: reduces both sides of sum_setIntegral_GL2_shift to fiber_count·∫_{D_N^PSL} (·)
  via `setIntegral_SL_tile_fd_eq_fdo` + `sum_SL_tile_eq_fiberwise_PSL_tile` +
  `slToPslQuot_fiberCard_eq` + `setIntegral_Gamma1_fundDomain_PSL_eq_sum`, then applies
  `IsFundamentalDomain.setIntegral_eq` via hα_fd.
  Axiom-check: only propext, Classical.choice, Quot.sound.

### [T205] petN_heckeT_p_diamond_shift_core (sorry, line 1163) — **EXPANDED INTO SUB-TICKETS**
- **Status**: expanded
- **File**: AdjointTheory.lean:1104
- **Depends on**: T205-a, T205-c, T205-d (new sub-tickets below)
- **Parallel**: no
- **Expansion rationale (2026-04-17)**: After analyzing the proof structure, T205 is
  ~200-300 LOC of intricate coset algebra. Decomposed into sub-tickets to make
  progress modular and enable parallel work. See T205-a, T205-c, T205-d below.
- **Note on T204**: Cannot be used directly. T204 requires α normalizes Γ₁(N) but
  individual T_p coset reps (α_b, M_∞) do NOT normalize Γ₁(N). The proof must work
  at the `peterssonInner` level with per-summand slash adjoint.
- **Description**: Fill the sorry at line 815. The statement:
  ```lean
  petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g)
  ```
  i.e., `petN(T_p f, g) = petN(⟨p⟩f, T_p g)`.

  **This is the hardest remaining sorry.** Two approaches:

  **Approach A (via T204)**: Apply T204 to the double coset operator [Γ₁[1,0;0,p]Γ₁].
  The element diag(1,p) normalizes Γ₁(N) up to the double coset structure.
  Use the identity adj(diag(1,p)) = diag(p,1), and the double coset factorization
  from T105: Γ₁(N)·diag(p,1)·Γ₁(N) = Γ₁(N)·diag(1,p)·Γ₁(N) · γ₀.
  This gives T_p* = T_p · ⟨p⁻¹⟩. Main challenge: packaging the double coset
  operator as a single GL₂⁺ slash to apply T204.

  **Approach B (direct petN manipulation)**: Work at the coset sum level.
  Key algebraic insight: for g ∈ S_k(Γ₁(N)) and α_b = [1,b;0,p]:
  ```
  g ∣[k] adj(α_b) = g ∣[k] [p,-b;0,1] = g ∣[k] [p,0;0,1]
  ```
  for all b (since [p,-b;0,1] = T(-b)·[p,0;0,1] and T(-b) ∈ Γ₁(N) acts trivially on g).
  Then [p,0;0,1] = γ₁⁻¹ · α_∞ · γ₀ (double coset identity), so
  g ∣[k] adj(α_b) = (g ∣[k] α_∞) ∣[k] γ₀ = ⟨p⁻¹⟩(g ∣[k] α_∞).

  This collapses the b-sum: all adj(α_b) terms give the same function.
  The proof then matches the (b,q) double sum between LHS and RHS using:
  - peterssonInner_slash_adjoint (per-summand, with domain q⁻¹ • fd)
  - The b-independence of adj(α_b) on Γ₁-forms
  - Domain reindexing via the coset permutation (as in petN_slash_invariant)

  **Both approaches need significant case-by-case matrix algebra.**
  Approach B avoids T204 entirely but requires working out the explicit
  reindexing bijection on (b, q) pairs.

- **Proof approach from DS**: DS Theorem 5.5.3 (page 186):
  α = [1,0;0,p], α' = [p,0;0,1], factor [p,0;0,1] using T105, conclude
  T_p* acts as T_p · ⟨p⁻¹⟩.
- **Estimated**: ~200-300 lines (was 80-120, revised after detailed analysis)

### [T205-a] Per-summand slash adjoint for T_p coset reps ✅
- **Status**: done (2026-04-18)
- **File**: AdjointTheory.lean:1129 (`peterssonInner_slash_adjoint_coset`) and
  :1192 (`peterssonInner_slash_adjoint_coset_right` — right variant via Hermitian)
- **Notes**: ~40 LOC each. Also added 3 supporting lemmas: `peterssonAdj_mul`
  (anti-multiplicativity from Matrix.adjugate_mul_distrib),
  `peterssonAdj_mapGL_SL_eq_inv` (adj = inv for SL elements),
  `peterssonInner_slash_adjoint_right` (right-slash version via Hermitian symmetry).
  Axiom-clean.

### [T205-d] Main assembly: petN_heckeT_p_diamond_shift_core proof
- **Status**: open (stuck on final combinatorial bijection, see below)
- **File**: AdjointTheory.lean (sorry at current line ~1586)
- **Depends on**: T205-a ✅ (both variants proved), triple product identity ✅
- **Parallel**: no

#### What's been accomplished (2026-04-18 session)

**Infrastructure closed sorry-free** (all axiom-clean):
- `sum_setIntegral_GL2_shift` (T204, ~75 LOC): fundamental domain tiling for GL₂⁺ shifts
- `petN_slash_adjoint_GL2` (T204 downstream, signature expanded)
- `peterssonInner_slash_adjoint_coset` (T205-a, ~40 LOC) + right variant via Hermitian
- `peterssonAdj_mul` (anti-multiplicativity of peterssonAdj)
- `peterssonAdj_mapGL_SL_eq_inv` (adj = inv for SL elements cast to GL)
- `peterssonInner_slash_adjoint_right` (via Hermitian symmetry)
- `peterssonInner_add_left` (via Hermitian symmetry)
- `adjointGamma1Rep` + `adjointGamma1Rep_mem_Gamma1` (explicit γ₁⁻¹ ∈ Γ₁(N))
- `T_p_lower_triple_product_matrix` (DS key identity: T_p_lower = γ₁⁻¹ · T_p_upper(0) · γ₀)
- `slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0` (CuspForm + ModularForm variants)

**T205-d proof scaffold** (lines 1222-1586 of AdjointTheory.lean):
1. `show` unfolds petN to explicit SL-coset sum over `SL(2,ℤ) ⧸ Gamma1 N`.
2. `h_Tpf`, `h_Tpg`: naive double-coset decomp via `heckeT_p_fun_eq_coset_sum`
   (⇑(T_p h) = heckeT_p_ut ⇑h + ⇑h ∣ M_∞).
3. `simp_rw [h_Tpf, h_Tpg]`: apply these on both sides of the goal.
4. `simp only [slash_M_infty_eq_diamond_slash_T_p_lower, SlashAction.add_slash]`:
   rewrite `h ∣ M_∞ = (⟨u⟩ h) ∣ T_p_lower` and distribute outer `∣ q⁻¹`.
5. `simp only [slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0_ModularForm]`:
   rewrite `(⟨u⟩ h) ∣ T_p_lower = ((⟨u⟩ h) ∣ T_p_upper(0)) ∣ γ₀`.

At this point, the goal is a clean "4-term symmetric adjoint" identity with γ₀ = adjointGamma0Rep exposed explicitly on both sides.

#### Where I'm stuck

The residual sorry is the **combinatorial coset bijection** matching LHS's `(b, q)` pairs to RHS's `(c, q')` pairs, where q runs over `SL(2,ℤ) ⧸ Γ₁(N)` and b, c run over `{0, ..., p-1}`.

**Why local algebraic moves don't close it**:
- Applying `petN_slash_invariant` with γ = adjointGamma0Rep to transform LHS/RHS is **circular**: substituting f' := ⟨u⟩⁻¹ f, g' := ⟨u⟩⁻¹ g reduces T205 to itself on (f', g').
- T205 symmetric form ⟺ asymmetric form `petN (T_p f) g = petN f (⟨u⟩⁻¹ T_p g)` via diamond unitarity + `heckeT_p_comm_diamondOp`. Both forms need the same combinatorial argument.
- The σ-reindex in `petN_slash_invariant` (PeterssonLevelN.lean:887) IS the template but its direct adaptation fails per-summand because `T_p_upper(0)` appearing after our rewrites **doesn't normalize Γ₁(N)**. So moving γ ∈ Γ₀(N) through the T_p_upper(0) slash isn't trivial.

**What's genuinely needed** (~80-150 LOC):
A σ-reindex `Equiv.sum_comp` on `SL(2,ℤ) ⧸ Γ₁(N)` that absorbs γ₀ together with the matrix identity `T_p_lower · α_b = p · shift(b)` (where shift(b) ∈ Γ₁(N)). The bijection matches summands via:
- σ(q) = ⟦q.out · γ₀⁻¹⟧ on the quotient
- Per summand, use `peterssonInner_slash_adjoint_coset` / `_right` + adjugate simplifications
- Explicit matrix bookkeeping: T_p_upper(c) · σ(q).out⁻¹ = γ₁ · T_p_upper(c') · q.out⁻¹ · γ₀⁻¹ for some c' ∈ {0,...,p-1}, γ₁ ∈ Γ₁(N)

The proof is analogous to Finset.sum_bij applied at the sum level with bijection (b,q)↦(c',σ(q)).

**Attempted strategies that failed**:
1. Direct `petN_slash_invariant` application — circular.
2. Diamond unitarity + `heckeT_p_comm_diamondOp` reduction — circular via substitution.
3. Per-summand `peterssonInner_slash_adjoint` transforms to "common form" — LHS/RHS each invariant under the transformations, so can't be unified by local moves.
4. M_∞ substitution via `slash_M_infty_eq_diamond_slash_T_p_lower` — helpful for the scaffold but doesn't resolve the bijection.
5. Triple product via T_p_lower = γ₁⁻¹·T_p_upper(0)·γ₀ — exposes γ₀ but still leaves the per-summand matching.

**Concrete next steps for a future session**:
1. Adapt the σ-reindex proof from `petN_slash_invariant` to our scaffolded goal.
2. Write the explicit bijection (b, q) ↦ (c(b, q), σ(q)) with c(b, q) computed by decomposing `γ₀⁻¹ · α_b · q.out⁻¹ · σ(q).out⁻¹⁻¹ ∈ Γ₁(N)`.
3. Use `Finset.sum_bij_nested` or similar to rewrite the sum.
4. Per-summand matching via slash action composition.

- **Estimated effort**: ~2-4 hour dedicated session with careful Lean matrix bookkeeping. All prerequisites are in place.
- **Proof outline** (analysis completed 2026-04-18):
  After applying T205-a / T205-a_right to both sides + slash_peterssonAdj simplifications,
  both reduce to a sum of 4 explicit summands (per q : SL(2,ℤ) ⧸ Γ₁(N)):

  LHS = ∑_q [Σ_b peterssonInner k (α_b • q⁻¹ • fd) f (g ∣ T_p_lower)
            + peterssonInner k (T_p_lower • q⁻¹ • fd) (⟨p⟩ f) (g ∣ T_p_upper(0))]

  RHS = ∑_q [Σ_c peterssonInner k (α_c • q⁻¹ • fd) ((⟨p⟩ f) ∣ T_p_lower) g
            + peterssonInner k (T_p_lower • q⁻¹ • fd) ((⟨p⟩ f) ∣ T_p_upper(0)) (⟨p⟩ g)]

  The summand matching requires:

  **Matrix identity** (for L_upper ↔ R_upper): `T_p_lower · α_b = p · shift(b)` where
  shift(b) ∈ Γ₁(N). This transforms L_upper tiles (T_p_lower • α_b • q⁻¹ • fd) into
  Γ₁(N)-translates of (q⁻¹ • fd). Matching L_upper ↔ R_upper then needs a bijection
  between (b, q) pairs on LHS and (c, q') pairs on RHS reflecting the double coset
  structure `Γ₁ diag(1,p) Γ₁ ↔ Γ₁ diag(p,1) Γ₁` via γ₀ ∈ Γ₀(N) (= `adjointGamma0Rep`).

  **For L_lower ↔ R_lower**: After applying `slash_M_infty_eq_diamond_slash_T_p_lower`
  (existing lemma: `f ∣ M_∞ = (⟨p⟩ f) ∣ T_p_lower`), both summands can be re-written
  in M_∞ form. The identity then reduces to a Hermitian/reindexing argument.

  **Key existing infrastructure** (all proved):
  - T205-a: `peterssonInner_slash_adjoint_coset` (and right variant)
  - `slash_peterssonAdj_T_p_upper_eq_T_p_lower` (b-independence)
  - `slash_peterssonAdj_T_p_lower_eq_T_p_upper_0`
  - `slash_M_infty_eq_diamond_slash_T_p_lower`
  - `sum_setIntegral_GL2_shift` (for domain reassembly under Γ₁(N)-normalizing shifts)
  - `peterssonInner_slash_adjoint_right`, `peterssonAdj_mul`, `peterssonAdj_mapGL_SL_eq_inv`

  **Remaining work**: The summand-matching bijection. Concretely needs a lemma
  relating `{(b, q) : SL(2,ℤ) ⧸ Γ₁(N) × [0, p)} ∪ {q}` to `{(c, q') : SL(2,ℤ) ⧸ Γ₁(N) × [0, p)} ∪ {q'}`
  via the γ₀ Γ₀(N) action. Needs either (a) direct matrix/coset algebra, or (b)
  a reduction to the abstract Hecke algebra's double-coset inverse identity.
- **Estimated**: ~80-150 lines (revised down: infrastructure is all there, main
  effort is the coset bijection)

---

## Open — Downstream (sorry #3, #4)

### [T206] heckeT_n_adjoint composite case (sorry #3) ✅
- **Status**: done (2026-04-13)
- **File**: AdjointTheory.lean:946
- **Notes**: Restructured entire heckeT_n_adjoint to use strong induction via
  `Nat.strong_induction_on`. Added 8 helper lemmas (lines 917-1170):
  `heckeT_n_cusp_comm_diamondOp`, `heckeT_n_cusp_decomp`, `heckeT_n_cusp_comm`,
  `diamondOp_cusp_comp`, `diamondOp_cusp_one`, `heckeT_n_adjoint_coprime_case`,
  `heckeT_n_cusp_ppow_recursion`, `heckeT_n_adjoint_ppow_case` + supporting helpers.
  Three cases: coprime factorization (n = p^v * m), prime (v=1), prime power (v≥2).
  The original sorry #3 at line 1010 is fully eliminated.
  Need the composite n case in the strong induction.

  **Proof strategy** (coprime factorization + prime-power recursion):

  The induction is on n. Write n = p^v · m where p = minFac(n), v = factorization(n,p),
  and gcd(p^v, m) = 1 (since m = n/p^v has all factors of p removed).

  **Case A (v = 1, m > 1)**: n = p · m with gcd(p, m) = 1.
  T_n = T_p · T_m (coprime factorization, `heckeT_n_mul_coprime`).
  ```
  petN(T_n f, g) = petN(T_p(T_m f), g)
                 = petN(T_m f, ⟨p⟩⁻¹ T_p g)           [heckeT_p_adjoint]
                 = petN(f, ⟨m⟩⁻¹ T_m(⟨p⟩⁻¹ T_p g))    [IH for m < n]
                 = petN(f, ⟨m⟩⁻¹ ⟨p⟩⁻¹ T_m T_p g)     [T_m commutes with ⟨p⟩⁻¹]
                 = petN(f, ⟨n⟩⁻¹ T_n g)                [⟨mp⟩ = ⟨m⟩⟨p⟩, T_n = T_m T_p]
  ```

  **Case B (v ≥ 2, m = 1)**: n = p^v, prime power.
  Use the recursion T_{p^v} = T_p · T_{p^{v-1}} - p^{k-1} · ⟨p⟩ · T_{p^{v-2}}.
  ```
  petN(T_{p^v} f, g)
    = petN(T_p(T_{p^{v-1}} f), g) - p^{k-1} petN(⟨p⟩(T_{p^{v-2}} f), g)
    = petN(T_{p^{v-1}} f, ⟨p⟩⁻¹ T_p g) - p^{k-1} petN(T_{p^{v-2}} f, ⟨p⟩⁻¹ g)
    = petN(f, ⟨p^{v-1}⟩⁻¹ T_{p^{v-1}}(⟨p⟩⁻¹ T_p g))
      - p^{k-1} petN(f, ⟨p^{v-2}⟩⁻¹ T_{p^{v-2}}(⟨p⟩⁻¹ g))     [IH for v-1, v-2]
    = petN(f, ⟨p^v⟩⁻¹ T_p T_{p^{v-1}} g - p^{k-1} ⟨p^{v-1}⟩⁻¹ T_{p^{v-2}} g)
    = petN(f, ⟨p^v⟩⁻¹ T_{p^v} g)                                [recursion]
  ```
  The last step uses: ⟨p^v⟩⁻¹ = ⟨p⟩⁻¹ · ⟨p^{v-1}⟩⁻¹ and
  ⟨p^{v-1}⟩⁻¹ = ⟨p^v⟩⁻¹ · ⟨p⟩ (diamond multiplicativity).

  **Case C (v ≥ 2, m > 1)**: Combine cases A and B.

  **Supporting lemmas needed**:
  - `petN_add_left'` (line 1100) — additivity ✓
  - `petN_smul_right` (PeterssonLevelN.lean:245) — scalar linearity ✓
  - `petN_conj_smul_left'` (line 1109) — conjugate-scalar ✓
  - `diamondOp_petersson_unitary` (line 711) — ⟨d⟩ unitary ✓
  - `heckeT_n_comm_diamondOp` (HeckeT_n.lean:2527) — T_n commutes with ⟨d⟩ ✓
  - `heckeT_n_mul_coprime` — coprime factorization ✓
  - `heckeT_ppow_succ_succ` — prime-power recursion ✓
  - Diamond multiplicativity for `ZMod.unitOfCoprime` — need to verify
- **Estimated**: ~60-80 lines

### [T207] exists_simultaneous_eigenform_basis (sorry #4, line 1325)
- **Status**: open
- **File**: AdjointTheory.lean:1270
- **Depends on**: T206 (via heckeT_n_adjoint)
- **Parallel**: partially (Mathlib API work can proceed before T206)
- **Description**: Fill the sorry at line 1325. Prove:
  ```lean
  ∃ (B : Finset (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)),
      (∀ f ∈ B, f ∈ cuspFormCharSpace k χ) ∧
      (∀ f ∈ B, IsCommonEigenfunctionCusp k f) ∧
      (∀ f g, f ∈ B → g ∈ B → f ≠ g → petN f g = 0)
  ```

  **Proof strategy** (3 steps):

  **Step 1: Joint eigenspace decomposition.**
  Define `T : CoprimeIndex N → Module.End ℂ (cuspFormCharSpace k χ)` where
  `CoprimeIndex N := { n : ℕ+ // Nat.Coprime n.val N }` and
  `T ⟨n, hn⟩ := heckeT_n_cusp_charRestrict k n.val hn χ`.

  Pairwise commutativity: from `heckeT_n_comm` (HeckeT_n.lean:1693, **fully proved**).
  Individual triangularizability: `heckeT_n_cusp_isSemisimple_on_charSpace` (line 1209).

  Apply Mathlib's
  `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`
  (from `Mathlib.LinearAlgebra.Eigenspace.Pi`) to get:
  `⨆ λ, ⨅ i, (T i).maxGenEigenspace (λ i) = ⊤`

  Since each T_i is triangularizable over ℂ (algebraically closed), and the generalized
  eigenspaces are eigenspaces when the operator is semisimple (which holds here since
  `iSup_maxGenEigenspace_eq_top` gives the full triangularization), every element of a
  joint (generalized) eigenspace is a simultaneous eigenform.

  **Step 2: Basis extraction.**
  From `⨆ λ, E_λ = ⊤` in a finite-dimensional space, the non-zero eigenspaces give a
  direct sum decomposition. Pick a basis from each non-zero E_λ (using
  `FiniteDimensional.exists_is_basis_finset` or `Submodule.exists_finset_of_eq_top`).
  Concatenate into a single `Finset`.

  **Step 3: Orthogonality.**
  For distinct eigenforms f, g with different eigenvalue tuples (∃ n with T_n f = λ_n f,
  T_n g = μ_n g, λ_n ≠ μ_n):
  ```
  λ_n · petN f g = petN(T_n f, g) = χ(n)⁻¹ · μ_n · petN f g
  ```
  (by `heckeT_n_adjoint_on_charSpace`). So (λ_n - χ(n)⁻¹ μ_n) · petN f g = 0.
  Since the eigenvalue tuples differ, λ_n ≠ χ(n)⁻¹ μ_n for some n, hence petN f g = 0.

  For eigenforms from the SAME joint eigenspace (f ≠ g but same eigenvalues):
  promote `petN_innerProductCore` to a full `InnerProductSpace` instance on
  `cuspFormCharSpace`, then apply Gram-Schmidt orthogonalization
  (`OrthonormalBasis.fromOrthogonalSpanMk` or manual construction).

  **Mathlib API needed** (all verified available):
  - `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_...` (Eigenspace.Pi)
  - `Module.End.iSup_maxGenEigenspace_eq_top` (Eigenspace.Triangularizable)
  - `InnerProductSpace.ofCore` (for promoting petN_innerProductCore)
  - `OrthogonalFamily` (InnerProductSpace.Subspace)
  - `LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces` (JointEigenspace)
    — may be usable if we twist T_n by χ(n)^{1/2} to make it symmetric

  **Alternative for orthogonality**: Instead of the symmetric operator API, use
  the manual argument above (5 lines per pair). This avoids needing to show
  the Hecke operators are symmetric (they're only "χ-twisted symmetric").

- **Estimated**: ~80-120 lines

---

## Open — Cleanup

### [T208] Fix stale comments and remove dead code
- **Status**: open
- **File**: AdjointTheory.lean
- **Depends on**: T207 (after all sorries are filled)
- **Parallel**: partially (comment fixes can happen anytime)
- **Type**: cleanup
- **Description**:
  1. Fix stale comments claiming `heckeT_n_comm` is sorry'd (lines 1266, 1284, 1323)
  2. Remove dead code block at lines 668-692 (superseded SL₂(ℝ) invariance comments)
  3. Clean up proof of `petN_heckeT_p_adjoint_unsymm` (lines 822-849) which duplicates
     `heckeT_p_adjoint_of_diamond_shift` (lines 865-896) — merge into one
  4. Run `/cleanup` on the full file
- **Estimated**: deletion + minor edits

---

## Dependency Graph

```
T201 (IsFundDomain Γ₁ tiling) ──→ T202 (petN = ∫_{D_N})
  │                                   │
  └──→ T203 (domain shift)  ──────────┘
                │
                └──→ T204 (petN_slash_adjoint_GL2, sorry #1)
                       │
                       └──→ T205 (petN_heckeT_p_diamond_shift_core, sorry #2)
                              │
                              └──→ T206 (heckeT_n_adjoint composite, sorry #3)
                                     │
                                     └──→ T207 (spectral theorem, sorry #4)
                                            │
                                            └──→ T208 (cleanup)
```

## Risk Assessment

| Ticket | Risk | Notes |
|--------|------|-------|
| T201 | Medium | Standard construction, but ±I subtlety for N ≤ 2 |
| T202 | Low | Direct unfolding + finite disjoint union |
| T203 | Low | Leverages Mathlib's `setIntegral_eq` directly |
| T204 | Low-Medium | Assembly of T202 + T203 + peterssonInner_slash_adjoint |
| T205 | **High** | Core combinatorial argument; explicit double coset reindexing |
| T206 | Medium | Algebraic induction, all supporting lemmas available |
| T207 | **High** | Mathlib API assembly; Finset basis extraction is fiddly |
| T208 | Low | Cleanup only |
