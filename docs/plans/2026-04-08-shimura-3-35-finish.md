# Plan: Finish Shimura Theorem 3.35

**Date**: 2026-04-08
**File**: `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke.lean`
**Goal**: Eliminate the last sorry at line 5047 in `T_1m_mem_ψ_range`.

## Current State

`shimura_thm_3_35` (line ~5238) is proved modulo a single sorry inside
`T_1m_mem_ψ_range`. The case is: `T'(1, p^k) ∈ range(ψ_hom N)` for prime `p ∤ N`
and `k ≥ 2`.

## Mathematical Strategy (Shimura Thm 3.34)

The approach is to extract `T'(1, p^k)` from the Hecke product
`T'(1, p) * T'(1, p^{k-1})` at the Gamma0(N) level via the formula:

```
T'(1, p) * T'(1, p^{k-1}) = T'(1, p^k) + c_{k-1} • T'(p, p^{k-1})
```

where `c_{k-1} = p+1` if `k-1 = 1` (i.e., `k = 2`), and `c_{k-1} = p` if `k ≥ 3`.

This is the Gamma0-level analogue of Shimura's identity 3.24(5) (proved at GL
level as `T_sum_prime_mul_T_ad` in `GL2/MultiplicationTable.lean:487`).

## Why This Is Hard

The Gamma0-level multiplication formula does NOT directly follow from the
GL-level formula because:

1. The Gamma0 Hecke ring multiplication uses Γ₀(N) decompQuots, not SL₂(ℤ)
   decompQuots.
2. The ring hom `shimura_ring_hom = ψ_hom ∘ π_hom⁻¹` maps GL basis elements
   to elements of the Gamma0 Hecke ring, but these images might not be
   "the corresponding Gamma0 basis elements" (the natural identification).

The IDENTIFICATION `shimura_ring_hom(T_elem(![a₀, a₁])) = T'(a₀, a₁)` for
`gcd(a₀, N) = 1` is a non-trivial fact equivalent to saying that the GL and
Gamma0 multiplication formulas agree on coprime-to-N inputs.

## Key Mathematical Fact

For prime `p ∤ N` and any `j ≥ 0`:

```
[Γ₀(N) : Γ₀(Np^j)] = [SL₂(ℤ) : Γ₀(p^j)] = ψ(p^j) = p^{j-1}(p+1)  (for j ≥ 1)
```

This follows from the CRT-induced bijection:

```
Γ₀(N)/Γ₀(Np^j) ≅ SL₂(ℤ)/Γ₀(p^j)
```

which holds because:
- `Γ₀(N) ∩ Γ₀(p^j) = Γ₀(Np^j)` (when `gcd(N, p) = 1`)
- `Γ₀(N) · Γ₀(p^j) = SL₂(ℤ)` (when `gcd(N, p) = 1`, by CRT)

The bijection extends to a correspondence between:
- Left coset reps of `H ⋅ diag(1, p^j) ⋅ H` at the Γ₀(N) level
- Left coset reps of `SL₂(ℤ) ⋅ diag(1, p^j) ⋅ SL₂(ℤ)` at the GL level

This in turn implies that the heckeMultiplicity values at the Gamma0 level
equal the GL level values (for coprime-to-N inputs), giving us the
multiplication formula.

## Phased Implementation Plan

### Phase 1: CRT bijection of decompQuots (~150 lines)

**Lemma**: For `gcd(N, p) = 1`, `j ≥ 1`:
```lean
private lemma Gamma0_decompQuot_bij_GL_decompQuot (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (j : ℕ) (hj : 1 ≤ j) :
    HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep
      (T_diag_Gamma0 N (![1, p^j]) _ _)) ≃
    HeckeRing.decompQuot (GL_pair 2) (HeckeCoset.rep (T_diag (![1, p^j])))
```

**Steps**:
1. Show `Γ₀(N) ∩ Γ₀(p^j) = Γ₀(Np^j)` for `gcd(N,p) = 1`. (This may already be
   `Gamma0_inf_eq_of_coprime` adapted to the case `m = 1, n = p^j`.)
2. Show `Γ₀(N) · Γ₀(p^j) = SL₂(ℤ)` for `gcd(N, p) = 1`. (This is the harder
   step; requires CRT for SL₂(ℤ/Np^j ℤ) ≅ SL₂(ℤ/Nℤ) × SL₂(ℤ/p^j ℤ).)
3. Build the bijection using the second isomorphism theorem:
   ```
   Γ₀(N)/(Γ₀(N) ∩ Γ₀(p^j)) ≅ Γ₀(N)·Γ₀(p^j)/Γ₀(p^j) = SL₂(ℤ)/Γ₀(p^j)
   ```

### Phase 2: Multiplicity transfer (~100 lines)

**Lemma**: For `gcd(p, N) = 1`, the Gamma0-level heckeMultiplicity equals the
GL-level heckeMultiplicity:

```lean
private lemma heckeMultiplicity_Gamma0_eq_GL_coprime
    (p : ℕ) (hp : p.Prime) (hpN : (p : ℤ).gcd N = 1)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (i : ℕ) (hi : 2*i ≤ j+k) :
    HeckeRing.heckeMultiplicity (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^j]) _ _))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) _ _))
      (HeckeCoset.rep (T_diag_Gamma0 N (![p^i, p^(j+k-i)]) _ _)) =
    HeckeRing.heckeMultiplicity (GL_pair 2)
      (HeckeCoset.rep (T_diag (![1, p^j])))
      (HeckeCoset.rep (T_diag (![1, p^k])))
      (HeckeCoset.rep (T_diag (![p^i, p^(j+k-i)])))
```

**Proof**: Use the bijection from Phase 1 to set up a `Set.Bijection` between
the counting sets of the two multiplicities. Show the bijection preserves the
mulMap condition.

### Phase 3: Gamma0-level multiplication formula (~80 lines)

**Lemma**: 
```lean
private lemma Gamma0_T1p_mul_T1ppow_coprime (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 1 ≤ k) :
    T_single (T_diag_Gamma0 N (![1, p]) _ _) 1 *
    T_single (T_diag_Gamma0 N (![1, p^k]) _ _) 1 =
    T_single (T_diag_Gamma0 N (![1, p^(k+1)]) _ _) 1 +
    (if k = 1 then ((p : ℤ) + 1) else (p : ℤ)) •
    T_single (T_diag_Gamma0 N (![p, p^k]) _ _) 1
```

**Proof**: 
1. Apply Phase 2 with j = 1 and the same k to get the multiplicity equalities.
2. Use the GL-level result `T_sum_prime_mul_T_ad` to get the GL multiplicities.
3. Conclude the Gamma0 multiplicities are 0, 1, p+1, p as required.
4. Show the support is exactly `{T'(1, p^(k+1)), T'(p, p^k)}` (no other terms).
5. Conclude the formula via `T_single_one_mul_eq_single` or direct Finsupp.ext.

### Phase 4: Fill the main sorry (~40 lines)

In `T_1m_mem_ψ_range` at line 5047:

```lean
· -- p coprime to N, k ≥ 2
  have hp_lt : p < p^k := ...
  have hpk1_lt : p^(k-1) < p^k := ...
  have hpk2_lt : p^(k-2) < p^k := ...
  have h_IHp := ih p hp_lt hp.pos
  have h_IHpk1 := ih (p^(k-1)) hpk1_lt (pow_pos hp.pos _)
  have h_IHpk2 := ih (p^(k-2)) hpk2_lt (pow_pos hp.pos _)
  -- T'(p, p^(k-1)) ∈ range via T_Gamma0_scalar_mul_gen
  have h_Tppk1_range : T_single (T_diag_Gamma0 N (![p, p^(k-1)]) _ _) 1 ∈ range := by
    -- T'(p, p) * T'(1, p^(k-2)) = T'(p, p^(k-1)) by T_Gamma0_scalar_mul_gen
    -- T'(p, p) ∈ range (generator), T'(1, p^(k-2)) ∈ range by IH
    sorry  -- minor formalization, mostly diagram chase
  -- Apply the helper from Phase 3
  have h_formula := Gamma0_T1p_mul_T1ppow_coprime N p hp hpN (k-1) (by omega)
  rw [show k - 1 + 1 = k from by omega] at h_formula
  -- T'(1, p^k) = T'(1,p) * T'(1, p^(k-1)) - c • T'(p, p^(k-1))
  have h_extract : T_single (T_diag_Gamma0 N (![1, p^k]) _ _) 1 = 
      T_single (T_diag_Gamma0 N (![1, p]) _ _) 1 *
      T_single (T_diag_Gamma0 N (![1, p^(k-1)]) _ _) 1 -
      (if k - 1 = 1 then ((p : ℤ) + 1) else (p : ℤ)) •
      T_single (T_diag_Gamma0 N (![p, p^(k-1)]) _ _) 1 :=
    eq_sub_of_add_eq h_formula.symm
  rw [h_extract]
  exact (ψ_hom N).range.sub_mem
    ((ψ_hom N).range.mul_mem h_IHp h_IHpk1)
    ((ψ_hom N).range.zsmul_mem h_Tppk1_range _)
```

## Total Estimated Effort

- Phase 1: ~150 lines (CRT bijection + helper lemmas)
- Phase 2: ~100 lines (multiplicity transfer)
- Phase 3: ~80 lines (Gamma0 multiplication formula)
- Phase 4: ~40 lines (use the formula to fill the sorry)
- **Total: ~370 lines of new code**

## Alternative Simpler Plan

Instead of the full bijection, take a more direct approach:

1. **Direct degree formula**: Prove `[Γ₀(N) : Γ₀(Np^j)] = ψ(p^j) = p^{j-1}(p+1)`
   for `gcd(N, p) = 1`, `j ≥ 1`. (~100 lines, uses tower formula + 
   `Gamma0_deg_coprime_mul`)

2. **Direct multiplicity bound**: Use the degree to derive `μ₀ ≤ (p+1)/p ≤ 1`
   in the specific case. Combined with `μ₀ ≥ 1` (identity pair), gives `μ₀ = 1`.
   (~50 lines)

3. **Support classification**: Show the only D in `mulSupport(rep T'(1,p),
   rep T'(1, p^{k-1}))` are `T'(p^j, p^{k-j})` for `0 ≤ j ≤ k/2`. (~30 lines,
   determinant + diagonal rep argument)

4. **Fill the sorry**: Extract `T'(1, p^k)` by subtraction. (~40 lines)

Total: ~220 lines.

## Files Touched

- `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke.lean` (main file, +220-370 lines)

No other files need modification.

## Pre-existing Issues

The file does not currently build standalone due to a pre-existing import
conflict between `LeanModularForms.HeckeRIngs.GLn.Projection` and
`LeanModularForms.HeckeRIngs.GLn.PolynomialRing` (both define
`HeckeRing.GLn.R_p_isPolynomialRing`). This needs to be resolved separately.
