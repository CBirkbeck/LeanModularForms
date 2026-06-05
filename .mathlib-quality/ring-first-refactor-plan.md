# Ring-first Hecke operator refactor — design + phase plan

**Goal (user-approved)**: the ring homs 𝕋(Γ₀(N)) → End(…) become the *construction* of the
Hecke operators; operator-level structure (comm, multiplicativity) is *transported* from the
commutative ring (CommRing via Atkin–Lehner anti-involution) through Φ_χ and glued over the
character direct sum; the ~1,080-LOC private induction cascade in HeckeT_n.lean is deleted.

## Facts established by recon (2026-06-05)

- `twistedHeckeSlash_gen` is χ-twisted by necessity: Γ₀(N)-classes act canonically only on
  χ-eigenspaces. The χ-free hom on M_k(Γ₁(N)) must be the **directSum glue** of
  `heckeRingHomCharSpace` over χ (via `ModularForm_Gamma1_charSpace_directSum`).
- Ring-side elements already exist in NebentypusHeckeRingHom.lean § CompositeBridge:
  `heckeRingDp p` (any p>0!), `heckeRingTpp p` (p ∤ N), `heckeRingD_ppow p` (recurrence,
  p ∤ N), `heckeRingD_n` (minFac assembly, **junk 0 at p | N**).
- Bridges proven (all p ∤ N / (n,N)=1): `heckeRingHomCharSpace_heckeRingDp` (= χ(p)⁻¹•T_p|_χ),
  `…_heckeRingTpp` (= χ(p)⁻¹p^{k-2}•1), `…_heckeRingD_ppow`, `…_heckeRingD_n`
  (= χ(n)⁻¹•heckeT_n_charRestrict), `heckeT_n_cusp_eq_heckeRingHom`.
- **Current arrow direction is wrong**: `heckeT_n_charRestrict_mul_coprime` (bridge file
  :1234) unfolds to operator-level `heckeT_n_mul_coprime`. Refactor inverts it.
- Consumer generality (agent audit): `heckeT_n_comm` consumed for ALL m,n (no coprimality
  to N) via private `heckeT_n_cusp_comm` (AdjointTheoryPetersson:74);
  `heckeT_n_mul` (general divisor-sum table, public ~:1850) consumed by FourierHecke
  (eigenform_coeff_multiplicative_one); `heckeT_n_comm_diamondOp` coprime-to-N only;
  `heckeT_ppow_*` recurrence lemmas needed unconditionally (incl. p | N where ⟨p⟩ = 0).
- `T_bad_mul` (ring, Props.lean:690): D-classes T'(1,m)·T'(1,n) = T'(1,mn) for m,n | N^∞ —
  the ring ALREADY has bad-class multiplication.
- Deletable cascade: HeckeT_n.lean lines ~600–1240 + 1294–1885 private support
  (~1,080 LOC; keep public statements as thin wrappers over transported proofs).

## Architecture decision

Extend `heckeRingD_n` to use genuine bad classes (`heckeRingDp p` for p | N, with
D_{p^r} := D_p^r matching `heckeT_ppow_eq_pow_of_not_coprime`) instead of junk 0.
Add the bad-prime bridge Φ_χ(D_p) = U_p|_χ (no χ-factor; p | N). Then every public
operator lemma transports at FULL current generality; no API narrowing.

Good-part notation: n₁(n) := ordCompl-style coprime-to-N part of n; extended composite
bridge: Φ_χ(D_n) = χ(n₁(n))⁻¹ • heckeT_n_charRestrict-general. Final headline:
`heckeRingHomGamma1 : 𝕋(Γ₀(N)) ℤ →+* Module.End ℂ (ModularForm (Γ₁(N)) k)` glued over χ,
and (def-flip, last) `heckeT_n := diamondOp(n₁(n)) ∘ heckeRingHomGamma1 (heckeRingD_n n)`,
with the old minFac assembly becoming theorem `heckeT_n_eq_assembly`.

## Phases (each compiles + commits before the next)

- **P1 ring layer**: new file `HeckeRIngs/GL2/Unified/HeckeRingDn.lean` (imports the ring,
  NOT the operators): move/redefine heckeRingDp/Tpp/D_ppow/D_n (bad primes genuine);
  prove in CommRing 𝕋(Γ₀(N)): comm (free), per-prime Chebyshev-style product identity
  D_{p^r}D_{p^s} = Σ_{i≤min} (p•S_p)^i D_{p^{r+s-2i}} (pure algebra induction; S_p := Tpp),
  bad-prime D_{p^r} = D_p^r, coprime multiplicativity D_m·D_n = D_{mn} (ALL m,n via
  minFac induction in CommRing), general divisor-sum table if needed by FourierHecke
  transport. Keep old names in the bridge file as deprecated aliases or re-exports.
- **P2 bad-prime bridge**: Φ_χ(D_p) = heckeT_p_all|_χ for p | N (twisted-slash computation
  analogous to `twisted_matches_T_p`; the U_p coset reps are the upper-triangulars only).
  Extend `heckeRingHomCharSpace_heckeRingD_n` to all n (χ(n₁) factor).
- **P3 glue**: directSum ext principle (endos agreeing on each modFormCharSpace summand are
  equal — via `ModularForm_Gamma1_charSpace_directSum` + Submodule.iSup_induction);
  headline hom `heckeRingHomGamma1`; characterization heckeT_n = ⟨n₁⟩ ∘ Φ̂(D_n).
- **P4 transport + delete**: replace proofs of heckeT_n_comm / heckeT_n_mul_coprime /
  heckeT_n_mul / heckeT_n_comm_diamondOp / heckeT_ppow_mul-family by ring transport
  (statements unchanged); fix `heckeT_n_charRestrict_mul_coprime` to come from the ring;
  delete the private cascade; rebuild downstream (AdjointTheoryPetersson, FourierHecke,
  SMOObligations, Newforms/LevelRaiseComm).
- **P5 def-flip (user wants this)**: heckeT_n defined via the ring hom; old assembly
  becomes `heckeT_n_eq_assembly`; patch downstream defeq-unfolds via the rewrite lemma.
  heckeT_p stays the explicit analytic atom.
- **P6 blueprint**: update HeckeOperators/CharacterSpaces chapters (heckeT-n entry now
  ring-constructed; uses-edges from heckeT-n-mult/comm to the ring entries), rebuild,
  push (CI deploys).

## Status log
- [x] Recon (P0) — 2026-06-05
- [x] P1 core — commit 0968732: `Unified/Gamma0RingDn.lean` sorry-free.
  Generic `formal_ppow_mul` (Chebyshev) + generic `peelProd`/`peelProd_mul_coprime`
  (CommMonoid) + concrete heckeRingDp/Spp/D_ppow/D_n/S_n with genuine bad classes.
  KEY TECHNIQUE: 𝕋 has global Ring + non-instance CommRing (instCommRing_Gamma0);
  `ring`/structural rw across the two paths FAILS (`*1+0` residue) — always prove
  generically over [CommRing R]/[CommMonoid R] and instantiate via
  `letI := instCommRing_Gamma0 N; exact generic …`.
- [x] P3a — commit 5b52cd2: `ModularForm_Gamma1_endo_ext` in CharacterDecomp.lean
  (endos agreeing on every modFormCharSpace are equal; via iSup_charSpace = ⊤ +
  Submodule.iSup_induction with motive named explicitly, LinearMap.ext not ext).
- [ ] P1b IN FLIGHT (bg agent ae5118a3): ring-side general table `heckeRingD_n_mul`
  in Gamma0RingDn.lean (divisor-sum, mirrors heckeT_n_mul_aux_noncoprime skeleton).
- [ ] P2 IN FLIGHT (bg agent a78fb799): bad-prime bridge in NebentypusHeckeRingHom
  area — `twisted_matches_T_p_bad` (p∣N: p upper reps, no lower, weight 1) +
  `heckeRingHomCharSpace_D_p_bad` (no χ-factor). May generalize private
  `adj_T_p_upper_factorisation`; cardinality via bad degree lemma or direct surjectivity.
- [ ] P3b AFTER P2: resolve NAME CLASH — bridge file's CompositeBridge defs
  (heckeRingDp/Tpp/D_ppow/D_n, OLD junk-0-at-bad-p versions) vs Gamma0RingDn's new
  ones (same namespace HeckeRing.GL2.Unified!). Plan: delete old defs from
  NebentypusHeckeRingHom.lean, import Gamma0RingDn, re-point the ~10 bridge proofs
  (good-prime bridge theorems heckeRingHomCharSpace_heckeRingD{p,_ppow,_n} survive
  with old signatures minus the hpN arg of D_ppow/Tpp — Tpp is now `if`-guarded
  `heckeRingSpp`, D_ppow recurrence now has `(p:ℤ)•Spp * d` not `(p:ℤ)•(Tpp * d)`).
  Newforms/Basic.isRingEigen references heckeRingD_n — semantics unchanged at
  coprime n (genuine blocks = old good blocks), bad-n semantics unobserved.
- [ ] P3c transports (needs P3b): per-χ END-level identities from the bridge
  (charRestrict X = χ(X)•Φ(D_X), products via map_mul + ring identities), then
  glue via ModularForm_Gamma1_endo_ext. Need general-n charRestrict
  (heckeT_p_all_preserves_modFormCharSpace already holds for ALL p —
  HeckeRingHomCharSpace.lean:81; extend heckeT_n_preserves_charSpace to all n).
- [x] P3b — commit 6abb11b: bridge re-pointed onto Gamma0RingDn (dupe defs deleted,
  _heckeRingTpp→_heckeRingSpp, total D_ppow bridge, downstream green). Bad-prime
  scaffold in place: ONE sorry in twisted_matches_T_p_bad (~:1061);
  heckeRingHomCharSpace_D_p_bad fully derived from it. Cardinality lemmas
  decompQuot_Npow_natcard / Gamma0_bad_deg de-privated in Props.lean.
- [~] P2-closer IN FLIGHT (bg agent a44869aaf): fill the twisted_matches_T_p_bad
  sorry (ψ : Fin p → decompQuot via T_p_upper factorisations — NOT adjugate;
  cardinality via Gamma0_bad_deg + D_p_Gamma0↔T_diag(1,p) conversion from
  HeckeCoset_deg_D_p_Gamma0's h_eq; weight bookkeeping via Delta0UpperUnit).
- [~] P3c WRITTEN BLIND (not yet compiled — closer owns the bridge file's build):
  Unified/RingTransport.lean (280 LOC): chiAllU (ℂˣ-valued good-part scalar via
  now-PUBLIC peelProd), heckeT_ppow_charRestrictAll + bad ppow bridge,
  charRestrictAll unfold, **extended bridge heckeRingHomCharSpace_heckeRingD_n_all**
  (Φ(D_n) = chiAllU⁻¹ • T_n|χ, all n), endo-level comm/mul_coprime, glued
  heckeT_n_comm_ring / heckeT_n_mul_coprime_ring / heckeT_n_comm_diamondOp_all.
  Also peelProd API publicized in Gamma0RingDn (edit pending rebuild).
  RISKY SPOTS to LSP-iterate: hT simpa alignment in bridge_all induction; bad-case
  smul alignment; Nat.not_dvd_ordCompl name; Module.End.mul_apply vs
  LinearMap.mul_apply.
- [ ] P4 (CYCLE-AWARE ORDER!): the bridge file's OLD composite chain
  (heckeRingHomCharSpace_heckeRingD_n + _step + heckeT_n_charRestrict_mul_coprime)
  depends on operator heckeT_n_mul_coprime → CANNOT delete the cascade while they
  live in the bridge file. Order:
  (a) finish RingTransport (needs closer); add general-table transport
      (needs: heckeRingS_n_eq_zero_of_not_coprime in Gamma0RingDn; Φ(heckeRingS_n d)
      scalar bridge by peel from _heckeRingSpp; chiAllU_eq_chi_of_coprime lemma via
      chi_unitOfCoprime_mul; divisor-sum bookkeeping) → transported heckeT_n_mul.
  (b) re-derive heckeT_n_cusp_eq_heckeRingHom + Eigenform consumers from bridge_all
      (move to RingTransport or keep via chiAllU_eq_chi_of_coprime), DELETE the old
      composite chain from the bridge file.
  (c) delete cascade from HeckeT_n.lean (audit ranges ~623-1920 minus ppow
      _zero/_one/_succ_succ/_eq_pow which STAY); move heckeT_n_preserves_charSpace
      alias into HeckeRingHomCharSpace.lean (REORDER: _all block must go ABOVE
      heckeT_n_charRestrict); re-declare deleted public names (heckeT_n_comm,
      heckeT_n_mul_coprime, heckeT_n_mul, heckeT_n_comm_diamondOp) with EXACT old
      names+signatures in RingTransport.lean under `namespace HeckeRing.GL2`.
  (d) consumer import fix-ups: AdjointTheoryPetersson, Unified/Gamma1CharSpace
      (uses heckeT_n_mul), FourierHecke (ppow lemmas stay — no change expected),
      Newforms/LevelRaiseComm (ppow — no change), SMOObligations.
- [ ] P5 def-flip: heckeT_n := ⟨goodPart n⟩ ∘ Φ̂(D_n) with glued hom Φ̂ (needs
  IsInternal-based assembly), old minFac assembly becomes heckeT_n_eq_assembly.
- [ ] P6 blueprint chapter updates + deploy.
