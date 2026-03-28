# Quotient Redesign Plan

Replace `structure HeckeCoset` (stores `carrier : Set G` + `∃ elt`) with
`Quotient dcSetoid` (quotient of `Δ` by `HgH = HhH`).

Prototype: `AbstractHeckeRing/Prototype.lean`
Branch: `hecke-ring` (starting from commit `f020880`)

## Key principle

Every proof that currently does `D.doubleCoset_eq.choose` becomes either:
- `D.out` (when we need a concrete rep from a `HeckeCoset`)
- `Quotient.inductionOn D fun g => ...` (when we can reduce to concrete `g : Δ`)

## Dependency order

```
Basic.lean          -- core types (MUST be first)
  ↓
Multiplication.lean -- mulMap, heckeMultiplicity, Mul instance
  ↓
Module.lean         -- smulOrbit, SMul instance, FaithfulSMul
  ↓
Associativity.lean  -- IsScalarTower (m'_uniform)
  ↓
Ring.lean           -- Ring instance + API
  ↓
Degree.lean         -- deg homomorphism
Commutativity.lean  -- AntiInvolution, CommRing
  ↓
GLn/*               -- all depend on AbstractHeckeRing
  ↓
GL2/*               -- depends on GLn
```

## Stages

### Stage 1: Basic.lean (SEQUENTIAL — everything else depends on this)

Replace the core types. This breaks ALL downstream files.

Changes:
- [ ] Delete `structure HeckeCoset` (old: carrier + doubleCoset_eq)
- [ ] Add `dcRel`, `dcSetoid`, `def HeckeCoset := Quotient dcSetoid`
- [ ] Add `DecidableEq` instance (Classical)
- [ ] Replace `HeckeCoset.mk'` with `⟦g⟧` (Quotient.mk)
- [ ] Replace `HeckeCoset.carrier` with `HeckeCoset.toSet` (via Quotient.lift)
- [ ] Replace `HeckeCoset_rep` with `HeckeCoset.rep` (= Quotient.out)
- [ ] Replace `HeckeCoset.one` with `⟦⟨1, Δ.one_mem⟩⟧`
- [ ] Port: `HeckeCoset_ext` → `Quotient.sound` / `Quotient.exact`
- [ ] Port: `HeckeCoset_set_eq_doubleCoset` → `toSet_mk` (definitional)
- [ ] Port: `HeckeCoset_rep_mem` → `rep_mem`
- [ ] Port: `T_one_choose_mem_H` etc. → lemmas about `(HeckeCoset.one P).out`
- [ ] Delete `structure HeckeLeftCoset` similarly → quotient of Δ by left coset rel
- [ ] Port `decompQuot` — change from using `.doubleCoset_eq.choose` to `D.out`
- [ ] Keep `HeckePair`, `𝕋`, `HeckeModule` unchanged (they're type aliases of Finsupp)

**Key decision**: `decompQuot` should be defined on `P.Δ` (not on `HeckeCoset`),
since the quotient type `H ⧸ (H ∩ gHg⁻¹)` depends on the specific `g`, and
lifting it to `HeckeCoset` requires proving the types are equal (not just isomorphic).
This is the approach in the prototype.

### Stage 2: Multiplication.lean (SEQUENTIAL — depends on Stage 1)

Port the multiplication machinery.

Changes:
- [ ] `decompQuot_T_one_eq_top` — uses `T_one_choose_mem_H` → port to quotient
- [ ] `decompQuot_coset_diff` — uses `.doubleCoset_eq.choose` → use `.out`
- [ ] `mulMap` — uses `D.doubleCoset_eq.choose` → use `g : P.Δ` directly
       (define on `P.Δ × P.Δ`, not on `HeckeCoset × HeckeCoset`)
- [ ] `heckeMultiplicity` — similarly, define on `P.Δ` args
- [ ] `mulSupport` — on `P.Δ` args, returns `Finset (HeckeCoset P)`
- [ ] `m` — the multiplication Finsupp, defined on `P.Δ` args
- [ ] `Mul` instance — uses `D.out` to extract reps from HeckeCoset
- [ ] `T_single`, `HeckeLeftCoset_single` — unchanged (Finsupp.single)
- [ ] Port all `m'_*` lemmas (now `heckeMultiplicity_*`)
- [ ] **NEW**: `heckeMultiplicity_well_defined` — prove multiplicity is independent of rep
       (this is the content of `heckeMultiplicity_uniform` + conjugation)

### Stage 3: Module.lean (SEQUENTIAL — depends on Stage 2)

Port the module action.

Changes:
- [ ] `smulOrbit` — uses `decompQuot` on a concrete `g : P.Δ`
       Change from using `D.doubleCoset_eq.choose` to `D.out` (where D : HeckeCoset)
- [ ] `SMul` instance — uses `.out` to get reps
- [ ] `single_smul_single` — port
- [ ] `smulOrbit_disjoint_of_ne` — port (this is the key lemma)
- [ ] `FaithfulSMul` — port

### Stage 4: Associativity.lean (SEQUENTIAL — depends on Stage 3)

The hardest file to port. `m'_uniform` is the key theorem.

Changes:
- [ ] `heckeMultiplicity_uniform` — the proof constructs explicit bijections
       between fiber sets. With the quotient design, `Quotient.inductionOn` replaces
       `obtain ⟨elt, helt⟩ := D.doubleCoset_eq`. The core combinatorial argument
       is the same.
- [ ] `IsScalarTower` — uses `heckeMultiplicity_uniform`
- [ ] `HeckeLeftCoset_ext_set` — already @[ext], just port

### Stage 5: Ring.lean + Degree.lean + Commutativity.lean (PARALLEL — depend on Stage 4)

These are relatively mechanical once Stages 1-4 are done.

**Ring.lean:**
- [ ] `mul_assoc_𝕋` — via FaithfulSMul + IsScalarTower (same proof)
- [ ] `Ring` instance — same structure
- [ ] All API lemmas — mechanical port

**Degree.lean:**
- [ ] `HeckeCoset_deg` — uses `decompQuot`, defined on `P.Δ` or uses `.out`
- [ ] `deg` ring homomorphism — same structure
- [ ] `smulOrbit_card` — port

**Commutativity.lean:**
- [ ] `AntiInvolution` — same structure
- [ ] `bar` → `onΔ` (acts on `P.Δ`)
- [ ] `onCoset` — `Quotient.lift` (cleaner than current `T'.mk'` approach)
- [ ] `heckeMultiplicity_comm_of_onCoset_eq` — same proof, cleaner with quotient

### Stage 6: GLn layer (PARALLEL agents, one per file — depend on Stage 5)

Each GLn file imports AbstractHeckeRing and needs mechanical porting.

**Can run in parallel:**
- [ ] `GLn/Basic.lean` — `GL_pair`, `intMat_to_delta`, etc.
- [ ] `GLn/DiagonalCosets.lean` — `T_diag`, `T_elem`, Smith normal form
- [ ] `GLn/CosetDecomposition.lean` — upper-triangular reps
- [ ] `GLn/CoprimeMul.lean` — coprime product
- [ ] `GLn/Degree.lean` — degree computations
- [ ] `GLn/TransposeAntiInvolution.lean` — CommRing instance
- [ ] `GLn/PrimeDecomposition.lean` — prime splitting
- [ ] `GLn/SLnTransvection.lean` — no changes needed (independent of HeckeCoset)

Main change pattern:
- `D.doubleCoset_eq.choose` → `D.out` (where `D : HeckeCoset`)
- `HeckeCoset.mk' P g` → `⟦g⟧`
- `HeckeCoset_ext P D₁ D₂ heq` → `Quotient.sound heq`
- `D.carrier` → `HeckeCoset.toSet P D`

### Stage 7: GL2 layer (PARALLEL agents — depend on Stage 6)

- [ ] `GL2/Basic.lean` — T_ad, T_pp, T_sum
- [ ] `GL2/MultiplicationTable.lean` — Shimura 3.24
- [ ] `GL2/HeckeAction.lean` — heckeSlash
- [ ] `GL2/HeckeModularForm.lean` — heckeOperator
- [ ] `GL2/Degree.lean` — degree formulas
- [ ] `GL2/CongruenceIndex.lean` — no HeckeCoset usage, likely no changes

### Stage 8: Cleanup + delete prototype

- [ ] Delete `Prototype.lean`
- [ ] Run `/cleanup` on changed files
- [ ] Verify full build
- [ ] Update PROJECT_OVERVIEW.md

## Risk mitigation

- Stages 1-4 are sequential and each breaks everything downstream.
  Work on them one at a time, verifying build at each stage (ignoring downstream).
- Stages 5-7 can be parallelized with agents.
- If a proof becomes too hard to port, we can temporarily `sorry` it and move on.
- The old code is preserved on commit `f020880` — we can always revert.

## Estimated effort

| Stage | Files | Effort | Can parallelize? |
|-------|-------|--------|-----------------|
| 1. Basic | 1 | Medium | No |
| 2. Multiplication | 1 | Hard | No |
| 3. Module | 1 | Medium | No |
| 4. Associativity | 1 | Hard | No |
| 5. Ring+Degree+Comm | 3 | Medium | Yes (3 agents) |
| 6. GLn | 8 | Medium | Yes (8 agents) |
| 7. GL2 | 5 | Medium | Yes (5 agents) |
| 8. Cleanup | all | Easy | Yes |
