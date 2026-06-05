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
- [ ] P1 … P6
