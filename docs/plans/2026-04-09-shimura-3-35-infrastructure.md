# Plan: Infrastructure for sorry-free Shimura Theorem 3.35

**Date**: 2026-04-09
**Status**: Research plan
**Owner**: open
**Blocker**: `Gamma0_T1p_mul_T1ppow_coprime` sorry at `CongruenceHecke.lean:5130`
**Prerequisite**: Fix pre-existing `PolynomialRing.lean:400` build error (Phase 0 below)

## Goal

Fill the single remaining sorry in `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke.lean` so that `shimura_thm_3_35 : ∃ φ : HeckeRing.𝕋 (GL_pair 2) ℤ →+* HeckeRing.𝕋 (Gamma0_pair N) ℤ, Function.Surjective φ` is axiom-clean for every `N` with `[NeZero N]`.

The sorried statement (the Γ₀(N)-level prime-power multiplication formula, Shimura Thm 3.24(5) at level N):
```lean
private lemma Gamma0_T1p_mul_T1ppow_coprime (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 1 ≤ k) :
    T'(![1, p]) * T'(![1, p^k]) = T'(![1, p^(k+1)]) +
      (if k = 1 then ((p : ℤ) + 1) else (p : ℤ)) • T'(![p, p^k])
```
where `T'(a) = HeckeRing.T_single (Gamma0_pair N) ℤ (T_diag_Gamma0 N a _ _) 1`.

## Exploration findings (verified 2026-04-09)

### 1. `stab_diag_eq_Gamma0` is referenced but NOT defined

`Gamma0_deg_coprime_mul` (CongruenceHecke.lean:3836-3838) invokes `stab_diag_eq_Gamma0 N m hm_pos` three times but no such definition exists anywhere in the repo. Most likely status:
- The proof of `Gamma0_deg_coprime_mul` is broken / was renamed.
- OR `stab_diag_eq_Gamma0` was inlined elsewhere and the references are stale.

**Action**: this must be resolved as part of Phase 1. Either define `stab_diag_eq_Gamma0` properly or refactor `Gamma0_deg_coprime_mul` to inline the stabilizer identification. Until resolved, `Gamma0_deg_coprime_mul` itself is suspect.

### 2. GL-level matrix helpers are level-agnostic

In `MultiplicationTable.lean`:
- `mulSupport_pp_det_eq` (line 177): purely matrix-level, takes generic `g₁ g₂ g₃ g₄ : GL (Fin 2) ℚ` and determinant hypotheses. **Reusable as-is.**
- `mulSupport_pp_dvd_p_aux` (line 192): purely matrix-level, takes `S_mid L' R' : SL₂(ℤ)`. **Reusable as-is.**
- `mulSupport_pp_dvd_p` (line 215): takes generic `D1c D2c i₀_gl j₀_gl : GL (Fin 2) ℚ` + decomposition hypotheses. **Reusable as-is.**
- `mulSupport_pp_case_split` (line 247): takes generic diagonal `a` and derives `T_diag a = T_diag (![1, p^(k+1)]) ∨ T_diag a = T_diag (![p, p^k])`. **The conclusion uses `T_diag` (a GL_pair 2 coset) but the argument itself is matrix-level.** Reusable if we rewrite via `Gamma0_exists_diag_rep` before applying.
- `heckeMultiplicity_deg_sum_eq` (line 343): **specialized to `HeckeCoset (GL_pair 2)`.** Needs generalization to work for `Gamma0_pair N`.

### 3. `decompQuot_double_H_equiv` is generic

Defined in `BlockBijection.lean:162` for generic Hecke pair `P`. Gives: for `g : P.Δ`, `h k : P.H`, the equivalence `decompQuot P g ≃ decompQuot P ⟨h * g * k, ...⟩`. Used at `CongruenceHecke.lean:1305` and in `Gamma0_deg_coprime_mul`.

### 4. No mathlib lemma for `[SL₂(ℤ) : Γ₀(p)] = p + 1`

Searched `Mathlib/NumberTheory/` — no direct index formula. The CongruenceSubgroups file defines `Gamma0` but does not compute its index in `SL(2, ℤ)`. **This needs to be proved from scratch.**

### 5. `MvPolynomial.eval₂_eq'` DOES exist in mathlib

At `Mathlib/Algebra/MvPolynomial/Eval.lean:76`. Signature:
```lean
theorem eval₂_eq' [Fintype σ] (g : R →+* S₁) (X : σ → S₁) (f : MvPolynomial σ R) :
    f.eval₂ g X = ∑ d ∈ f.support, g (f.coeff d) * ∏ i, X i ^ d i
```
The pre-existing `PolynomialRing.lean:400` error is NOT a renaming issue — it's a semantic mismatch. See Phase 0 below.

### 6. `ψ_surjective`, `shimura_ring_hom`, `shimura_ring_hom_surjective` all defined AFTER line 5130

This means any proof of `Gamma0_T1p_mul_T1ppow_coprime` that uses `shimura_ring_hom` would require:
- Either moving the definition of `shimura_ring_hom` earlier (which requires untangling dependencies — it depends on `ker_π_le_ker_ψ` which is at line 4740, so this is possible).
- Or inlining the definition locally inside the proof.

**This rules out using `shimura_ring_hom` as a black box in the proof** unless we restructure the file.

### 7. Circularity of the `shimura_ring_hom` approach is confirmed

Applying `shimura_ring_hom` to the GL identity `T_sum(p) · T_ad 1 p^k = T_ad 1 p^(k+1) + c_k · T_ad p p^k` gives an equation in `𝕋(Γ₀(N))`, but the terms are `shimura_ring_hom(T_ad 1 p^k)` etc. — not `T'(1, p^k)`. Proving `shimura_ring_hom(T_ad 1 p^k) = T'(1, p^k)` by induction on `k` requires the Γ₀ identity itself at step `k-1` (or equivalent). **This approach is fundamentally circular without additional input.**

## Mathematical strategy

The cleanest formalization path is **Option 2** from the existing docstring: direct Γ₀(N) degree values via CRT, combined with the level-agnostic matrix helpers. Specifically:

1. Prove `Γ₀(N) · Γ₀(m) = SL₂(ℤ)` for `gcd(m, N) = 1` (group decomposition, follows from `Gamma_gcd_eq_mul`).
2. Apply the second isomorphism theorem to get `[Γ₀(N) : Γ₀(mN)] = [SL₂(ℤ) : Γ₀(m)]`.
3. Prove `[SL₂(ℤ) : Γ₀(p^k)] = p^(k-1)(p + 1)` directly (explicit coset reps via upper-triangular + anti-diagonal).
4. Chain 2 + 3 to compute all Γ₀ degrees for prime powers coprime to N.
5. Generalize `heckeMultiplicity_deg_sum_eq` to arbitrary Hecke pairs.
6. Transfer `mulSupport_pp_subset` to Γ₀ via Prop 3.31 injectivity + generic matrix helpers.
7. Prove `D_out1` is in the Γ₀ mulSupport (positivity, direct construction).
8. Assemble the main lemma following the GL proof template (`heckeMultiplicity_values`) with Γ₀ degrees substituted.

## Phase 0: Fix the pre-existing PolynomialRing build error

**Blocker**: `LeanModularForms/HeckeRIngs/GLn/PolynomialRing.lean:400` fails with `simp made no progress`.

**Diagnosis**: The goal at line 400 (inside `evalHom_injective_one`) is:
```
Finsupp.toFun (MvPolynomial.eval₂Hom (Int.castRingHom (HeckeAlgebra 1))
  (fun k => T_gen 1 p k) R) D = MvPolynomial.coeff s R
```

The simp call is:
```lean
simp only [MvPolynomial.eval₂_eq', Fin.prod_univ_one, T_gen_pow_one p hp]
```

The problem: `eval₂_eq'` rewrites `f.eval₂ g X` but the goal has `eval₂Hom ... R` applied at `D`, not `f.eval₂`. The `eval₂Hom` is a `RingHom` wrapper, and `Finsupp.toFun` applied to it doesn't match `eval₂_eq'`'s LHS pattern.

**Fix**: insert `show (MvPolynomial.eval₂Hom ... R).toFun D = MvPolynomial.coeff s R` and then either:
- use `MvPolynomial.eval₂Hom_eq_eval₂` / `MvPolynomial.coe_eval₂Hom` to reduce `eval₂Hom` to `eval₂`, then apply `eval₂_eq'`
- or rewrite the `show` to unfold `eval₂Hom` definitionally (`change (∑ d ∈ R.support, ...) D = _`) and skip `eval₂_eq'` entirely

Concrete candidate fix:
```lean
show (∑ d ∈ R.support,
    (fun k => T_gen 1 p k) 0 ^ d 0 * (Int.castRingHom _ (R.coeff d)) *
      (∏ i, (fun k => T_gen 1 p k) i ^ d i)) D = _
```
— but this is fragile. Better: extract an intermediate `have` that expresses the evaluation as a sum using `MvPolynomial.eval₂Hom_apply` + `eval₂_eq'`.

**Estimated complexity**: short (5-15 lines of refactoring).

**Must be done first** — until resolved, no Lean proof in CongruenceHecke.lean can be verified.

## Phase 1: Fix `stab_diag_eq_Gamma0` and repair `Gamma0_deg_coprime_mul`

**Objective**: ensure `Gamma0_deg_coprime_mul` compiles and gives the claimed coprime-degree multiplicativity. This is a dependency of `T_coprime_mul`, which is already used downstream.

### 1.1 Define `stab_diag_eq_Gamma0`

**Location**: CongruenceHecke.lean, just before `Gamma0_deg_coprime_mul` (~line 3740).

**Statement**:
```lean
/-- The conjugation stabilizer of `diag(1, m)` in `(Gamma0_pair N).H` equals
    the preimage of `Γ₀(mN)` under `mapGL ℚ`, viewed as a subgroup of `Γ₀(N)`. -/
private lemma stab_diag_eq_Gamma0 (N : ℕ) [NeZero N] (m : ℕ) (hm_pos : 0 < m) :
    (HeckeRing.conjSub (Gamma0_pair N)
      ⟨diagMat 2 (![1, m]),
        diagMat_mem_Delta0_of_gcd N _
          (fun i => by fin_cases i <;> simp [hm_pos]) (by simp)⟩) =
    ((CongruenceSubgroup.Gamma0 (m * N)).map (mapGL ℚ)).subgroupOf (Gamma0_pair N).H
```

**Proof strategy**: direct matrix-level computation, showing `σ ∈ Γ₀(N)` satisfies `diag(1, m)⁻¹ · σ · diag(1, m) ∈ Γ₀(N)` iff `m · N ∣ σ 1 0`. Use `diagConj_10` (already in file at line ~3529) which computes the (1,0) entry.

**Estimated LOC**: 30-50.

### 1.2 Verify `Gamma0_deg_coprime_mul` compiles

Once `stab_diag_eq_Gamma0` is in place, the lemma should compile. If there are further issues (eg. the stabilizer rewrite uses `Subgroup.quotientEquivOfEq`), adjust accordingly.

**Estimated LOC**: 0-20 (fixes).

## Phase 2: `SL₂(ℤ) = Γ₀(N) · Γ₀(m)` for coprime `m, N`

**Objective**: prove the group product decomposition that enables the second isomorphism theorem.

### 2.1 Group product decomposition

**Location**: CongruenceHecke.lean, near `Gamma0_mN_mul_GammaN_eq_Gamma0` (~line 3675).

**Statement**:
```lean
private lemma Gamma0_N_mul_Gamma0_m_eq_SL2 (N m : ℕ) [NeZero N] [NeZero m]
    (hcop : Nat.Coprime m N) :
    ∀ γ : SL(2, ℤ),
      ∃ (σ_N : SL(2, ℤ)) (σ_m : SL(2, ℤ)),
        σ_N ∈ CongruenceSubgroup.Gamma0 N ∧
        σ_m ∈ CongruenceSubgroup.Gamma0 m ∧
        γ = σ_N * σ_m
```

**Proof strategy**:
1. Use `Gamma_gcd_eq_mul m N` to get `Γ(1) = SL(2, ℤ) = Γ(m) · Γ(N)` (since `gcd(m, N) = 1` and `Γ(1) = SL₂`).
2. Any `γ ∈ SL(2, ℤ)` factors as `γ = α · β` with `α ∈ Γ(m) ⊂ Γ₀(m)`, `β ∈ Γ(N) ⊂ Γ₀(N)`.
3. Swap order: want `γ = σ_N · σ_m`, which is `β' · α'` for some `β' ∈ Γ₀(N)`, `α' ∈ Γ₀(m)`. Use `α · β = β · (β⁻¹ α β)` and normality of `Γ(m)` in SL₂. Since `β ∈ Γ(N)` is a unit modulo both `m` and `N`, `β⁻¹ α β ∈ Γ(m)` (Γ(m) is normal in SL₂). So `γ = β · (β⁻¹ α β)` with `β ∈ Γ₀(N)`, `β⁻¹ α β ∈ Γ₀(m)`. ✓

**Estimated LOC**: 40-60.

### 2.2 Second isomorphism theorem consequence

**Location**: right after 2.1.

**Statement**:
```lean
/-- For gcd(m, N) = 1: `[Γ₀(N) : Γ₀(mN)] = [SL₂(ℤ) : Γ₀(m)]`. -/
private lemma Gamma0_N_index_Gamma0_mN_eq_SL2_index_Gamma0_m
    (N m : ℕ) [NeZero N] [NeZero m] [NeZero (m * N)] (hcop : Nat.Coprime m N) :
    ((CongruenceSubgroup.Gamma0 (m * N)).subgroupOf
      (CongruenceSubgroup.Gamma0 N)).index =
    (CongruenceSubgroup.Gamma0 m).index
```

**Proof strategy**: apply `Subgroup.index_inf_eq_index_of_mul_eq_top` (or the equivalent mathlib second iso theorem statement) with `H = Γ₀(N)`, `K = Γ₀(m)`, `HK = SL₂` (from 2.1). Then `Γ₀(N) / (Γ₀(N) ∩ Γ₀(m)) ≃ SL₂ / Γ₀(m)`, and `Γ₀(N) ∩ Γ₀(m) = Γ₀(mN)` by `Gamma0_inf_eq_of_coprime` (already proved at line 3580).

**Mathlib API needed**: `Subgroup.card_eq_card_quotient_mul_card_subgroup`, `Subgroup.index_inf`, `Subgroup.relindex_mul_top`. Some of these may require searching mathlib for the exact name. Most likely target: `Subgroup.relindex_eq_relindex_of_isComplement` or `Subgroup.relindex_mul_mul_eq_mul_of_mul`.

**Estimated LOC**: 20-40.

## Phase 3: `[SL₂(ℤ) : Γ₀(p^k)] = p^(k-1)(p + 1)` for prime `p`

**Objective**: compute the SL₂-level index for prime powers directly. This is a standard number-theoretic fact but is not in mathlib.

### 3.1 Explicit coset representatives

**Location**: new file `LeanModularForms/HeckeRIngs/GLn/Gamma0Index.lean` (or inline in CongruenceHecke.lean if preferred).

**Intermediate lemma**:
```lean
/-- Standard coset representatives for SL₂(ℤ) / Γ₀(p^k):
    - Upper-triangular type: [[1, b], [0, 1]] reduced mod p^k, for b in a set of
      p^k/gcd values.
    - "Anti-diagonal" / involution type: S · T^j for j = 0, ..., p^(k-1) - 1. -/
```

Actually, the cleanest approach is via the orbit-stabilizer for SL₂(ℤ) acting on `P¹(ℤ/p^k ℤ) = (ℤ/p^k ℤ)²/~`. The stabilizer of `[0 : 1]` is `Γ₀(p^k)`, and `|P¹(ℤ/p^k ℤ)| = p^(k-1)(p+1)` (counts pairs `(a, c)` with `gcd(a, c, p^k) = 1` modulo scaling by `(ℤ/p^k ℤ)×`).

### 3.2 `[SL₂(ℤ) : Γ₀(p)] = p + 1` (base case)

**Location**: same file.

**Statement**:
```lean
private lemma SL2_index_Gamma0_prime (p : ℕ) (hp : p.Prime) :
    (CongruenceSubgroup.Gamma0 p).index = p + 1
```

**Proof strategy**: 
Option A (orbit-stabilizer): define the action of SL₂(ℤ) on `P¹(𝔽_p)` via reduction. Stabilizer of `[0:1]` = `Γ₀(p)`. `|P¹(𝔽_p)| = p + 1`. Use orbit-stabilizer (transitivity via SL₂(𝔽_p) acting transitively on P¹(𝔽_p)).

Option B (direct enumeration): SL₂(ℤ)/Γ₀(p) = {[[1,0],[0,1]], [[1,0],[1,1]], [[1,0],[2,1]], ..., [[1,0],[p-1,1]], [[0,-1],[1,0]]}. Prove these are distinct and cover.

Option B requires ~80 lines of matrix bash. Option A is cleaner but needs orbit-stabilizer setup.

**Estimated LOC**: 80-120.

### 3.3 `[SL₂(ℤ) : Γ₀(p^k)] = p^(k-1)(p+1)` (general)

**Location**: same file.

**Statement**:
```lean
private lemma SL2_index_Gamma0_prime_power (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 0 < k) :
    (CongruenceSubgroup.Gamma0 (p ^ k)).index = p ^ (k - 1) * (p + 1)
```

**Proof strategy**:
1. For `k ≥ 2`: show `[Γ₀(p) : Γ₀(p^k)] = p^(k-1)` (the finer subgroup has index `p^(k-1)` in the coarser).
2. Combine with 3.2: `[SL₂ : Γ₀(p^k)] = [SL₂ : Γ₀(p)] · [Γ₀(p) : Γ₀(p^k)] = (p+1) · p^(k-1)`.

For step 1, use `Γ₀(p) / Γ₀(p^k)`: the cosets are parameterized by `σ 1 0 / p` modulo `p^(k-1)` (since `σ ∈ Γ₀(p)` has `σ 1 0 = p · t` for some `t ∈ ℤ`, and two elements are in the same coset iff `t ≡ t' (mod p^(k-1))`). Gives `p^(k-1)` representatives.

**Estimated LOC**: 60-100.

## Phase 4: Γ₀(N) degrees for prime powers coprime to N

**Objective**: compute `deg_Γ₀(T'(1, p^k))` and `deg_Γ₀(T'(p^j, p^k))` for `gcd(p, N) = 1`.

### 4.1 `deg_Γ₀(T'(1, p^k)) = p^(k-1)(p+1)`

**Location**: CongruenceHecke.lean, after Phase 2-3 results.

**Statement**:
```lean
private lemma Gamma0_deg_one_ppow (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hpN : Nat.Coprime p N) (k : ℕ) (hk : 0 < k) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, p ^ k])
        (fun i => by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) = (p ^ (k - 1) * (p + 1) : ℤ)
```

**Proof strategy**:
1. Reduce to `[Γ₀(N) : Γ₀(p^k · N)]` via `stab_diag_eq_Gamma0` (Phase 1) and `decompQuot_double_H_equiv`.
2. Apply Phase 2.2 to get `[Γ₀(N) : Γ₀(p^k · N)] = [SL₂(ℤ) : Γ₀(p^k)]` (requires `gcd(p^k, N) = 1`, which follows from `gcd(p, N) = 1`).
3. Apply Phase 3.3.

**Estimated LOC**: 30-50.

### 4.2 `deg_Γ₀(T'(p^j, p^k)) = p^(k-j-1)(p+1)` for `j < k`, `gcd(p, N) = 1`

**Location**: same.

**Statement**:
```lean
private lemma Gamma0_deg_ppow_ppow (N p : ℕ) [NeZero N] (hp : p.Prime)
    (hpN : Nat.Coprime p N) (j k : ℕ) (hjk : j < k) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![p ^ j, p ^ k]) ...) =
    (p ^ (k - j - 1) * (p + 1) : ℤ)
```

**Proof strategy**: use `T_Gamma0_scalar_mul_gen` (already proved) to factor `T'(p^j, p^k) = T'(p^j, p^j) · T'(1, p^(k-j))`. Apply degree multiplicativity (from `deg` being a ring hom) + `Gamma0_HeckeCoset_deg_scalar` for the scalar factor + 4.1 for the `T'(1, p^(k-j))` factor.

**Estimated LOC**: 20-40.

### 4.3 Edge case: `deg_Γ₀(T'(p, p))` for `gcd(p, N) = 1`

Already handled by `Gamma0_HeckeCoset_deg_scalar` which gives degree 1 for any scalar matrix. Just need to note this in the main proof.

## Phase 5: Generalize `heckeMultiplicity_deg_sum_eq`

**Objective**: allow the degree sum formula to be used at the Γ₀ level.

### 5.1 Generic `heckeMultiplicity_deg_sum_eq`

**Location**: probably `AbstractHeckeRing/Multiplication.lean` (since it's level-agnostic).

**Statement**:
```lean
lemma HeckeRing.heckeMultiplicity_deg_sum_eq {P : HeckePair G}
    (D1 D2 D_out1 D_out2 : HeckeCoset P)
    (h_ne : D_out1 ≠ D_out2) (h_zero : ∀ A, A ≠ D_out1 → A ≠ D_out2 →
      HeckeRing.heckeMultiplicity P (HeckeCoset.rep D1) (HeckeCoset.rep D2)
        (HeckeCoset.rep A) = 0) :
    HeckeRing.heckeMultiplicity P (HeckeCoset.rep D1) (HeckeCoset.rep D2)
      (HeckeCoset.rep D_out1) * HeckeCoset_deg P D_out1 +
      HeckeRing.heckeMultiplicity P (HeckeCoset.rep D1) (HeckeCoset.rep D2)
        (HeckeCoset.rep D_out2) * HeckeCoset_deg P D_out2 =
      HeckeCoset_deg P D1 * HeckeCoset_deg P D2
```

**Proof**: the existing proof at `MultiplicationTable.lean:343` works verbatim after replacing `GL_pair 2` with `P`. The proof uses only generic Hecke ring properties: `T_single_one_mul_T_single_one`, `deg_mul`, `deg_T_single`, `mulSupport`, `heckeMultiplicity_eq_zero_of_nmem_mulSupport`. All of these are generic.

**Estimated LOC**: 30-40 (mostly moving the existing proof + small adaptations).

### 5.2 Replace the GL-specific version

Update `MultiplicationTable.lean` to use the generic version. Delete or deprecate the GL-specific copy.

**Estimated LOC**: 5-10 (just a reference update).

## Phase 6: Γ₀-level `mulSupport_pp_subset`

**Objective**: transfer the GL-level support restriction to Γ₀.

### 6.1 Γ₀ mulSupport containment

**Location**: CongruenceHecke.lean, before `Gamma0_T1p_mul_T1ppow_coprime`.

**Statement**:
```lean
private lemma mulSupport_pp_subset_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 0 < k)
    (A : HeckeCoset (Gamma0_pair N))
    (hA : A ∈ HeckeRing.mulSupport (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) ...))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p ^ k]) ...))) :
    A = T_diag_Gamma0 N (![1, p^(k+1)]) ... ∨ A = T_diag_Gamma0 N (![p, p^k]) ...
```

**Proof strategy**:
1. Apply `Gamma0_exists_diag_rep` to get A's diagonal rep `(d₁, d₂)` with `d₁ | d₂`, `gcd(d₁, N) = 1`.
2. Extract the product element from the mulSupport witness (pair `(i₀, j₀) ∈ decompQuot × decompQuot`).
3. Extract SL₂(ℤ) witnesses for the representatives of T_diag_Gamma0 (analogous to `T_diag_rep_decompose` but at Γ₀ level — may need a helper `T_diag_Gamma0_rep_decompose`).
4. Apply the generic `mulSupport_pp_det_eq`, `mulSupport_pp_dvd_p`, `mulSupport_pp_case_split` helpers to get `T_diag(d₁, d₂) = T_diag(1, p^(k+1)) ∨ T_diag(p, p^k)` at the GL level.
5. Apply `diagonal_representative_unique` to deduce `(d₁, d₂) = (1, p^(k+1)) ∨ (p, p^k)` as tuples.
6. Use `T_diag_Gamma0_ext` (uniqueness of Γ₀-coset from tuple) to conclude `A` is the corresponding Γ₀ coset.

**Dependency**: needs a helper `T_diag_Gamma0_rep_decompose` — see 6.2.

**Estimated LOC**: 80-120.

### 6.2 `T_diag_Gamma0_rep_decompose` helper

**Location**: CongruenceHecke.lean, near the other decomposition helpers.

**Statement**:
```lean
private lemma T_diag_Gamma0_rep_decompose (N : ℕ) [NeZero N] (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) :
    ∃ (L R : GL (Fin 2) ℚ) (σ_L σ_R : SL(2, ℤ)),
      L = mapGL ℚ σ_L ∧ R = mapGL ℚ σ_R ∧
      σ_L ∈ CongruenceSubgroup.Gamma0 N ∧
      σ_R ∈ CongruenceSubgroup.Gamma0 N ∧
      HeckeCoset.rep (T_diag_Gamma0 N a ha hgcd) = L * diagMat 2 a * R
```

**Proof strategy**: similar to the GL-level `T_diag_rep_decompose`, but extract witnesses in `Γ₀(N)` rather than `SL₂(ℤ)`. Use `HeckeCoset.rep_mem` to get the double coset membership, then extract.

**Estimated LOC**: 30-60.

## Phase 7: `D_out1 ∈ Γ₀ mulSupport` (positivity)

**Objective**: show `T'(1, p^(k+1))` is actually hit by the product (so multiplicity ≥ 1).

### 7.1 Positivity at D_out1

**Location**: CongruenceHecke.lean, before `Gamma0_T1p_mul_T1ppow_coprime`.

**Statement**:
```lean
private lemma D_out1_pp_in_mulSupport_Gamma0 (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 0 < k) :
    T_diag_Gamma0 N (![1, p^(k+1)]) ... ∈ HeckeRing.mulSupport (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) ...))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) ...))
```

**Proof strategy**: mirror the GL-level `D_out1_pp_in_mulSupport` (`MultiplicationTable.lean:316`). Extract L₁, R₁, L₂, R₂ decompositions at Γ₀ level (using 6.2), then use witnesses `h₁ = L₁⁻¹, h₂ = R₁⁻¹ · L₂⁻¹` in the Γ₀(N) subgroup. The key: `L₁⁻¹`, `R₁⁻¹`, `L₂⁻¹` must all be in `Γ₀(N)`, which follows from 6.2 giving Γ₀(N) witnesses.

**Estimated LOC**: 40-60.

## Phase 8: Main lemma — `Gamma0_T1p_mul_T1ppow_coprime`

**Objective**: assemble everything to fill the sorry.

### 8.1 The main proof

**Location**: CongruenceHecke.lean:5130 (replace the sorry).

**Proof strategy** (mirrors `heckeMultiplicity_values` + `T_sum_prime_mul_T_ad` at GL level):
1. Set up `D_1 := T'(1,p), D_2 := T'(1, p^k), D_out1 := T'(1, p^(k+1)), D_out2 := T'(p, p^k)`.
2. Apply `T_single_one_mul_eq_single_add_smul` (or a new helper) — OR work with `Finsupp.ext` directly.
3. Reduce the LHS to `HeckeRing.m D_1.rep D_2.rep` via `T_single_one_mul_T_single_one`.
4. Reduce to showing `HeckeRing.m` as a Finsupp equals `Finsupp.single D_out1 1 + Finsupp.single D_out2 c_k`.
5. Use `Finsupp.ext`:
   - At `A = D_out1`: multiplicity equals 1 (from degree sum + positivity).
   - At `A = D_out2`: multiplicity equals `c_k` (from degree sum - 1·deg(D_out1)).
   - At `A ≠ D_out1, D_out2`: multiplicity = 0 (from 6.1).
6. For the degree sum step, use:
   - `heckeMultiplicity_deg_sum_eq` (generic version from Phase 5)
   - Γ₀ degree values from Phase 4
   - `D_out1 ≠ D_out2` at Γ₀ level (via `cosetMap` injectivity + GL-level `h_ne` from `heckeMultiplicity_values`, OR direct via diagonal uniqueness)
   - `μ_1 ≥ 1` from Phase 7
   - `nlinarith` to pin down exact values (same arithmetic as the GL proof).

**Estimated LOC**: 150-250.

### 8.2 Verification

Once the proof compiles, verify:
- `lake build LeanModularForms.HeckeRIngs.GLn.CongruenceHecke` succeeds.
- `#print axioms shimura_thm_3_35` shows only standard axioms (no `sorryAx`).

## Summary table

| Phase | Objective | Files touched | LOC estimate |
|-------|-----------|---------------|--------------|
| 0     | Fix `PolynomialRing.lean:400` | PolynomialRing.lean | 5-15 |
| 1     | Define `stab_diag_eq_Gamma0`, repair `Gamma0_deg_coprime_mul` | CongruenceHecke.lean | 30-70 |
| 2     | `SL₂(ℤ) = Γ₀(N)·Γ₀(m)` + second iso | CongruenceHecke.lean | 60-100 |
| 3     | `[SL₂ : Γ₀(p^k)] = p^(k-1)(p+1)` | Gamma0Index.lean (new) | 140-220 |
| 4     | Γ₀ degrees for prime powers | CongruenceHecke.lean | 50-90 |
| 5     | Generalize `heckeMultiplicity_deg_sum_eq` | AbstractHeckeRing/Multiplication.lean | 35-50 |
| 6     | Γ₀ mulSupport containment + helpers | CongruenceHecke.lean | 110-180 |
| 7     | Γ₀ mulSupport positivity at D_out1 | CongruenceHecke.lean | 40-60 |
| 8     | Main lemma assembly | CongruenceHecke.lean | 150-250 |

**Total estimate**: ~620-1035 lines of new Lean code.

## Critical path

```
Phase 0 ──┐
          ├─→ Phase 1 ──→ (enables T_coprime_mul verification)
          │
          ├─→ Phase 2 ──→ needs Phase 1 (stab_diag_eq_Gamma0)
          │
          └─→ Phase 3 ──→ independent of Phases 1-2
                            │
                            └─→ Phase 4 ──→ needs Phases 2, 3
                                              │
                                              │   Phase 5 (independent)
                                              │   Phase 6 ──→ needs Phase 1
                                              │   Phase 7 ──→ needs Phase 6
                                              │
                                              └─→ Phase 8 ──→ needs 4, 5, 6, 7
```

**Recommended execution order**: 0 → (1, 3, 5 in parallel) → 2 → 4 → 6 → 7 → 8.

Phases 1, 3, 5 can be done in parallel by separate workers as they don't depend on each other once Phase 0 unblocks the build.

## Risks and open questions

1. **Mathlib API for second iso theorem**: the exact lemma name for computing quotient indices via complementation may take trial and error. Likely candidates: `Subgroup.relindex_sup_right`, `Subgroup.relindex_inf_mul_relindex`, `Subgroup.index_mul_of_le`. Worst case, prove the specific instance directly via `Subgroup.card_eq_card_quotient_mul_card_subgroup`.

2. **Normality of Γ(m) in SL₂** needed in Phase 2.1: this is a standard fact but should be verified — the `CongruenceSubgroup.Gamma_normal` instance in mathlib should suffice.

3. **Orbit-stabilizer for P¹(𝔽_p)** in Phase 3.2: if the "orbit-stabilizer" approach is too heavyweight, fall back to direct coset enumeration (more tedious but more elementary).

4. **Γ₀(p^k) index in Γ₀(p)** in Phase 3.3: alternative is to derive from the general formula `[SL₂ : Γ₀(N)] = N · ∏_{p|N}(1 + 1/p)` if it exists in mathlib, but I doubt it does.

5. **Heartbeat / elaboration issues**: the main lemma (Phase 8) will likely need `set_option maxHeartbeats` bumps. Existing pattern in CongruenceHecke.lean uses `set_option maxHeartbeats 1600000` and `3200000` for the heavy lemmas.

6. **`decompQuot_card_eq_of_mk_eq`**: referenced in the plan (in the existing proof docstring of `T_Gamma0_scalar_mul`) but may or may not exist. Verify in Phase 0/1.

## Alternative path: skip the infrastructure via polynomial lifts

A lighter alternative is to prove a helper `shimura_ring_hom_T_elem_coprime_det` by induction on `∏ a`, which sidesteps the degree computation but reintroduces the "prime power case" circularity. As documented in the existing docstring, this path fails at `(1, p^k)` for `k ≥ 2, p ∤ N`. **Not recommended** unless a breakthrough idea resolves the circularity.

## What gets unblocked when this is done

- `shimura_thm_3_35` becomes sorry-free.
- `ψ_surjective` becomes sorry-free.
- `T_1m_mem_ψ_range` becomes sorry-free.
- Downstream usages of `shimura_ring_hom_surjective` in `HeckeT_n.lean` (coprime multiplication, currently one of three blocked sorries) can proceed.
- Phase 3 Hecke T_n work (per `.mathlib-quality/tickets.md`) is unblocked at the level-N side.
