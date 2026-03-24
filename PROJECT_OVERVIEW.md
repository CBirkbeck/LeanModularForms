# Project Overview: HeckeRIngs

Generated: 2026-03-23 | Branch: `hecke-ring` | Mathlib: v4.28.0

## Summary
- **Files**: 21 (+ 1 re-export module file)
- **Total declarations**: ~578
- **Sorries**: 2 (both in `GLn/PolynomialRing.lean`)
- **maxHeartbeats annotations**: 3 (all in `GL2/HeckeModularForm.lean`: 400k, 400k, 6.4M)
- **Lines of code**: ~8,400

## Architecture

```
AbstractHeckeRing/   -- Generic Hecke ring for any arithmetic group pair (H, Delta)
       |
    GLn/             -- GL_n(Q) with H = SL_n(Z), Delta = pos-det integer matrices
       |
    GL2/             -- n=2: multiplication table, Hecke operators on modular forms
```

## Import Graph

```
AbstractHeckeRing/Basic
  <- Multiplication <- Module <- Associativity <- Ring <- {Commutativity, Degree}

GLn/Basic <- DiagonalCosets <- {CosetDecomposition, CoprimeMul, TransposeAntiInvolution}
  CoprimeMul <- {Degree (via CosetDecomposition + CongruenceIndex), PrimeDecomposition}
  PrimeDecomposition <- PolynomialRing
  TransposeAntiInvolution uses AbstractHeckeRing/Commutativity

GL2/Basic <- GLn/PrimeDecomposition
  GL2/Basic <- {MultiplicationTable, HeckeAction} <- HeckeModularForm
```

---

## AbstractHeckeRing/ (7 files, ~218 decls, ~2,872 lines)

### Basic.lean (291 lines, 46 decls)

Core structures and double-coset infrastructure.

- `struct ArithmeticGroupPair` -- Hecke pair (H, Delta) with H <= Delta <= commensurator(H)
- `struct T'` -- A double coset HgH with g in Delta
- `struct M` -- A left coset gH with g in Delta
- `def T'_rep` -- Chosen Delta-representative
- `def T_mk / M_mk` -- Constructors
- `def T_one / M_one` -- Identity cosets
- `def T / M_type` -- Hecke ring/module types (Finsupp to Z)
- `abbrev decompQuot` -- H/(H cap gHg^-1) indexing left cosets in a double coset
- Key API: `T'_ext`, `doubleCoset_eq_iUnion_leftCosets`, `doubleCoset_mul_eq_iUnion_doubleCoset`

### Multiplication.lean (501 lines, 36 decls)

Hecke multiplication via structure constants.

- `def mulMap` -- Maps (i,j) pair to product double coset
- `def m'` -- Shimura's multiplicity: Nat.card of pairs giving target coset
- `def mulSupport` -- Finset of double cosets in D1*D2
- `def m` -- Multiplication Finsupp
- `instance Mul (T P Z)` -- Convolution multiplication
- `abbrev T_single / M_single` -- Basis elements
- Key API: `m'_pos_of_mem`, `m'_eq_zero_of_nmem_mulSupport`, `m'_eq_one_of_le_one_and_pos`, `decompQuot_coset_diff`

### Module.lean (619 lines, 38 decls)

Left-coset module action and faithfulness.

- `def smulOrbit` -- Orbit of a left coset under double coset action
- `instance SMul (T P Z) (M P Z)` -- Module action
- `instance FaithfulSMul` -- Distinct ring elements act differently
- Key API: `smul_eq_sum`, `single_smul_single`, `smulOrbit_disjoint_of_ne`

### Associativity.lean (697 lines, ~15 decls)

Proves the module action is associative (Shimura Prop 3.4).

- `lemma m'_uniform` -- Multiplicity is uniform across coset reps (115 lines)
- `instance IsScalarTower` -- x . (y . z) = (y * x) . z

### Ring.lean (158 lines, 31 decls)

Ring structure and public API.

- `lemma T_mul_assoc` -- Via faithfulness + IsScalarTower
- `instance Ring (T P Z)` -- Full ring structure
- API: `T_single_zero/add/neg/sub/smul`, `T_single_mul_T_single`, `T.induction_on/linear`

### Degree.lean (195 lines, 24 decls)

Degree ring homomorphism (Shimura Prop 3.3).

- `def T'_deg` -- [H : H cap gHg^-1]
- `def deg` -- Ring hom T P Z ->+* Z
- Key: `T'_deg_pos`, `smulOrbit_card`, `deg_fun_mul`

### Commutativity.lean (411 lines, 29 decls)

Commutativity via anti-involutions (Shimura Prop 3.8).

- `struct AntiInvolution` -- Anti-automorphism preserving H, Delta, involutive
- `def bar / onT'` -- Underlying function and induced action on T'
- `theorem mul_comm_of_antiInvolution` -- CommRing when iota fixes all double cosets
- `def instCommRing_of_antiInvolution` -- CommRing instance

---

## GLn/ (9 files, ~243 decls, ~5,045 lines)

### Basic.lean (410 lines, 25 decls)

Concrete arithmetic group pair for GL_n(Q).

- `abbrev SLnZ_subgroup` -- SL_n(Z) as subgroup of GL_n(Q)
- `def HasIntEntries / posDetInt_submonoid` -- Integer entries + positive det
- `lemma posDetInt_le_commensurator` -- **Shimura Lemma 3.10** (53 lines)
- `def GL_pair` -- Standard Hecke pair
- `abbrev HeckeAlgebra` -- T'(GL_pair n) Z

### DiagonalCosets.lean (1,272 lines, 53 decls)

Smith normal form and diagonal representatives.

- `def diagMat / DivChain / T_diag / T_elem` -- Core definitions
- `theorem exists_diagonal_of_posdet` -- Smith normal form (171 lines)
- `theorem exists_diagonal_representative` -- Every Delta element has diagonal rep with DivChain
- `theorem diagonal_representative_unique` -- Elementary divisors are unique
- `theorem T_diag_span` -- Hecke algebra spanned by T_diag elements

### CosetDecomposition.lean (376 lines, 23 decls)

Upper-triangular coset representatives (Shimura Prop 3.22).

- `def UpperTriRep / upperTriMat / upperTriGL` -- Bounded upper-tri assignments
- `theorem upperTriGL_mem_doubleCoset` -- Each rep in correct double coset
- `theorem upperTriMat_distinct_cosets` -- Distinct entries -> distinct cosets (50 lines)

### CongruenceIndex.lean (271 lines, 21 decls)

- `theorem Gamma0_prime_index` -- [SL_2(Z) : Gamma_0(p)] = p + 1
- `theorem Gamma0_prime_power_index` -- [SL_2(Z) : Gamma_0(p^k)] = p^{k-1}(p+1)

### Degree.lean (565 lines, 24 decls)

- `def gaussianBinom` -- Gaussian binomial (currently unused)
- `theorem T'_deg_T_diag_two_prime` -- deg(T(p^i,p^{i+k})) = p^{k-1}(p+1) for n=2
- `theorem T'_deg_T_diag_two_scalar` -- deg(T(c,c)) = 1

### CoprimeMul.lean (1,584 lines, 53 decls) -- Largest file

- `theorem SLnZ_transvec_gen` -- SL_n(Z) = product of transvections
- `lemma SLnZ_CRT_decomposition` -- CRT for SL_n
- `theorem T_diag_mul_coprime` -- **Shimura Prop 3.16** (156 lines)
- `theorem T_diag_scalar_mul` -- **Shimura Prop 3.17**

### TransposeAntiInvolution.lean (121 lines, 11 decls)

- `def GL_transposeEquiv / GL_pair_antiInvolution`
- `lemma GL_pair_onT'_eq` -- Transpose fixes every double coset
- `instance instCommRing_HeckeAlgebra` -- **Shimura Prop 3.8 for GL_n**

### PrimeDecomposition.lean (292 lines, 20 decls)

- `def ppowDiag / pComponent / removePrime / R_p`
- `theorem T_elem_split_prime` -- Factor into p-power and p-free parts
- `theorem HeckeAlgebra_generated_by_R_p` -- Full algebra = join of all R_p

### PolynomialRing.lean (154 lines, 13 decls) -- **2 SORRIES**

- `def T_gen / evalHom` -- Generators and evaluation map
- `theorem T_gen_generates_R_p` -- **SORRY** (surjectivity)
- `def R_p_isPolynomialRing` -- **SORRY** (Shimura Thm 3.20: R_p ~ Z[X_1,...,X_n])

---

## GL2/ (4 files, ~117 decls, ~2,692 lines)

### Basic.lean (419 lines, 22 decls)

- `def T_ad / T_pp / T_sum` -- GL_2 Hecke notation
- `theorem T_elem_mul_scalar` -- T(b) * T(c,...,c) = T(bc)
- `lemma T_pp_comm_T_elem / T_pp_pow` -- Diamond operator algebra

### MultiplicationTable.lean (1,540 lines, 48 decls)

Shimura 3.24 theorems:

- `theorem thm324_2` -- T(1,p^k) = T(p^k) - diamond*T(p^{k-2})
- `theorem thm324_5` -- T(p)*T(1,p^k) = T(1,p^{k+1}) + c*T(p,p^k) (62 lines)
- `theorem T_sum_ppow_recurrence` -- Three-term recurrence (40 lines)
- `theorem thm324_4` -- **General prime-power product** (92 lines)
- `theorem T_sum_mul_coprime` -- **Coprime multiplicativity** (41 lines)
- `theorem thm324_3` -- **General product formula** (46 lines)
- `theorem thm324_7` -- **deg(T(m)) = sigma_1(m)**

### HeckeAction.lean (386 lines, 34 decls)

- `def heckeSlash` -- Sum over left coset reps of f|[k] tRep(D,i)
- `lemma heckeSlash_slash_invariant` -- Preserves Gamma-invariance
- `def heckeSlashInvariant` -- Produces SlashInvariantForm

### HeckeModularForm.lean (347 lines, 13 decls)

- `def heckeOperator` -- T(D) : ModularForm -> ModularForm
- `def heckeOperatorLinear` -- T(D) as C-linear map
- `theorem heckeSlash_comp` -- **T(D1)(T(D2)(f)) = (D2*D1)(f)** (54 lines)
- Note: `set_option maxHeartbeats 6400000` on `heckeSlash_fiber_sum`

---

## Consolidation Analysis

### Sorries (blocking completeness)

| Sorry | Location | Description |
|-------|----------|-------------|
| `T_gen_generates_R_p` | PolynomialRing:144 | Surjectivity of evaluation hom (hard) |
| `R_p_isPolynomialRing` | PolynomialRing:150 | R_p ~ Z[X_1,...,X_n] (Shimura Thm 3.20) |

### Duplicate Code

- `intMat_det_cast` appears privately in GLn/Basic:83, CosetDecomposition:150, DiagonalCosets:177 -- extract to shared utility

### Unused Declarations

- `gaussianBinom` (Degree.lean:51) -- defined but never used
- `T_ad'` (GL2/Basic:84) -- deprecated alias

### Large Proofs (decomposition candidates)

| Proof | File | Lines |
|-------|------|-------|
| `exists_diagonal_of_posdet` | DiagonalCosets | 171 |
| `T_diag_mul_coprime` | CoprimeMul | 156 |
| `m'_uniform` | Associativity | 115 |
| `gcd_step_general` | DiagonalCosets | 105 |
| `T_sum_mul_peel_prime_aux` | MultiplicationTable | 95 |
| `thm324_4` | MultiplicationTable | 92 |

### Shimura Coverage

| Reference | Status | Location |
|-----------|--------|----------|
| Prop 3.3 (degree hom) | Done | AbstractHeckeRing/Degree |
| Prop 3.4 (associativity) | Done | AbstractHeckeRing/Associativity |
| Prop 3.8 (commutativity) | Done | Commutativity + GLn/TransposeAntiInvolution |
| Lemma 3.10 (commensurator) | Done | GLn/Basic |
| Prop 3.16 (coprime product) | Done | GLn/CoprimeMul |
| Prop 3.17 (scalar product) | Done | GLn/CoprimeMul |
| Prop 3.22 (coset decomposition) | Done | GLn/CosetDecomposition |
| **Thm 3.20 (R_p ~ Z[X_1,...,X_n])** | **SORRY** | GLn/PolynomialRing |
| Thm 3.24(2-7) | Done | GL2/MultiplicationTable |
| Hecke operators on modular forms | Done | GL2/HeckeAction + HeckeModularForm |
| Composition = algebra mult | Done | GL2/HeckeModularForm |
