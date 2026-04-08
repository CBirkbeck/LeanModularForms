# Plan: Finish Shimura Theorem 3.35

**Date**: 2026-04-08 (updated 2026-04-08 after reading Shimura)
**File**: `LeanModularForms/HeckeRIngs/GLn/CongruenceHecke.lean`
**Goal**: Eliminate the sorry in `Gamma0_T1p_mul_T1ppow_coprime`.

## Shimura's Actual Approach (pp. 67-71)

After consulting Shimura's *Introduction to the Arithmetic Theory of Automorphic
Functions* §3.3, here is the actual proof strategy:

### Key Theorem: Proposition 3.31 (the "Δ_N isomorphism")

> The correspondence `Γ'αΓ' ↦ ΓαΓ`, with `α ∈ Δ'_N`, defines an **isomorphism** of
> `R(Γ', Δ'_N)` onto `R(Γ, Δ_N)`.

Where:
- `Γ' = Γ₀(N)` (the level-N congruence subgroup)
- `Γ = SL₂(ℤ)` (the full modular group)
- `Δ'_N = {[u v; w z] ∈ Δ | u coprime to N, w ≡ 0 (N), (z, N) = 1}` — the
  "level-N primitive Δ"
- `Δ_N` is the SL₂(ℤ)-level analogue (`{α ∈ Δ | similar conditions}`)
- `Δ*_N = {α ∈ Δ | λ_N(α) = [1 0; 0 x] for x ∈ (ℤ/N)^×}` — even more restrictive

The isomorphism is the natural collapsing map. Its inverse exists because of the
CRT-type lifting argument.

### How Shimura uses Prop 3.31 (p. 71)

Shimura derives the Gamma0-level multiplication formula directly:

> "By (1) and (5) of Th. 3.24, and by **Prop. 3.31**, we have
> `pT'(p, p) = T'(p)² - T'(p²)` for every prime p not dividing N"

For higher prime powers:

> "Thus the multiplication of the elements `T'(n)` can be reduced to that of
> `T'(p^k)` with a prime p. If p divides N, we have `T'(p^k) = T'(p)^k`. If
> `(p, N) = 1`, the elements `T'(p^k)` satisfy the same formulas as in Th. 3.24,
> **on account of Prop. 3.31**."

So Shimura's proof of the Gamma0 multiplication formulas is essentially:
1. Apply the inverse isomorphism `R(Γ, Δ_N) → R(Γ', Δ'_N)` to the GL identity
2. The identity transfers because both sides live in the restricted Hecke rings
   that are isomorphic via Prop 3.31

### Proof of Prop 3.31 (Shimura p. 67-68)

**Surjectivity**: Let `η ∈ Δ_N`, `b = det(η)`. Take integer `c` with `bc ≡ 1 (mod N)`,
put `φ = [1 0; 0 c]`. Then `det(ηφ) ≡ 1 (mod N)`. By Lemma 1.38 (CRT for SL₂),
there exists `γ ∈ Γ` with `γ ≡ ηφ (mod N)`. Then `γ⁻¹η ∈ Δ*_N`, and `Γγ⁻¹ηΓ = ΓηΓ`.
This proves the inverse map exists.

**Injectivity**: Let `α, β ∈ Δ*_N` with `α ≡ β (mod N)`. If `ΓαΓ = ΓβΓ`, then by
Lemma 3.29(1), `Γ'αΓ' = Γ'βΓ'`. (`R(Γ', Δ'_N)` is a free Z-module.)

## Current State (after Shimura Prop 3.31 implementation)

**Both parts of Shimura's Proposition 3.31 are now proved:**
- `shimura_prop_3_31` (line 784): injectivity of cosetMap on coprime-det cosets
- `shimura_prop_3_31_surjective` (line 4099): every coprime-det GL coset has a
  Γ₀(N) preimage. **Just added.**

These two lemmas together give the **full bijection** between coprime-det
Γ₀(N)-double cosets and coprime-det SL₂(ℤ)-double cosets (Shimura's Prop 3.31).

**Status of `shimura_thm_3_35`**: Proved modulo a single sorry in
`Gamma0_T1p_mul_T1ppow_coprime`, the Gamma0-level prime-power multiplication
formula:

```
T'(1,p) * T'(1, p^k) = T'(1, p^(k+1)) + c_k • T'(p, p^k)
```

where `c_k = p+1` if `k=1`, `c_k = p` if `k ≥ 2`. This is the Gamma0-level
analogue of `T_sum_prime_mul_T_ad` (Shimura 3.24(5)).

## Remaining Work: Multiplicity Equality

To fill the helper lemma sorry, the **multiplication formula transfer** still needs:

**Key Lemma** (multiplicity equality for coprime det):
```lean
private theorem heckeMultiplicity_Gamma0_eq_GL_coprime
    (g₁ g₂ : (Gamma0_pair N).Δ) (D : HeckeCoset (Gamma0_pair N))
    (h_g₁ h_g₂ h_D : coprime det conditions) :
    HeckeRing.heckeMultiplicity (Gamma0_pair N) g₁.val g₂.val (HeckeCoset.rep D) =
    HeckeRing.heckeMultiplicity (GL_pair 2)
      (Delta0_inclusion N g₁) (Delta0_inclusion N g₂)
      (HeckeCoset.rep (cosetMap N D))
```

The proof requires showing the bijection on decompQuots:
`Γ₀(N) / (Γ₀(N) ∩ g Γ₀(N) g⁻¹) ≅ SL₂(ℤ) / (SL₂(ℤ) ∩ g SL₂(ℤ) g⁻¹)` for g with
coprime det. This follows from `Γ₀(N) · (SL₂(ℤ) ∩ g SL₂(ℤ) g⁻¹) = SL₂(ℤ)` for
the coprime case (a CRT-style argument similar to `Gamma_gcd_eq_mul`).

Once this multiplicity equality is established, the helper lemma follows by:
1. `Finsupp.ext` on the multiplication formula
2. For each Γ₀(N) coset D, compute the multiplicity via the equality lemma + the
   GL formula (`T_sum_prime_mul_T_ad`)
3. The support classification follows from `shimura_prop_3_31_surjective` +
   `shimura_prop_3_31`

## Implementation Plan: Shimura's Prop 3.31 Approach

The cleanest path is to formalize Shimura's Proposition 3.31 directly: the
isomorphism `R(Γ₀(N), Δ'_N) ≅ R(SL₂(ℤ), Δ_N)` for the level-N "primitive"
Hecke rings. Then transfer the GL identity `T_sum_prime_mul_T_ad` to the
Gamma0 level via the inverse isomorphism.

### Phase A: Define the level-N "primitive" subset Δ_N (~30 lines)

Define a sub-semigroup `Delta_N_primitive ⊆ Delta0_submonoid N` consisting of
matrices `[a b; c d]` with `a coprime to N`, `c ≡ 0 (mod N)`, `d coprime to N`.

(In Shimura's notation: this is `Δ'_N` for `Γ' = Γ₀(N)`.)

### Phase B: Define the SL₂(ℤ)-level analogue (~30 lines)

Define `Delta_N_SL2 ⊆ Delta_submonoid` (the level-1 Hecke Δ) consisting of
matrices satisfying the same conditions on `a, c, d` mod N.

### Phase C: Build the isomorphism Prop 3.31 (~150 lines)

The isomorphism `R(Γ₀(N), Delta_N_primitive) ≅ R(SL₂(ℤ), Delta_N_SL2)` via
`[Γ₀(N)αΓ₀(N)] ↦ [SL₂(ℤ)αSL₂(ℤ)]`. Key steps:

1. **Show the natural map is well-defined**: Each Γ₀(N)-double coset maps to a
   unique SL₂(ℤ)-double coset.
2. **Show injectivity**: For `α, β ∈ Delta_N_primitive` (with reduction `≡ I (mod N)`),
   if `[SL₂(ℤ)αSL₂(ℤ)] = [SL₂(ℤ)βSL₂(ℤ)]`, then `[Γ₀(N)αΓ₀(N)] = [Γ₀(N)βΓ₀(N)]`.
   Uses Shimura's Lemma 3.29(1).
3. **Show surjectivity**: For any `η ∈ Delta_N_SL2`, find `γ ∈ SL₂(ℤ)` such that
   `γ⁻¹η ∈ Delta_N_primitive` and `[SL₂γ⁻¹ηSL₂] = [SL₂ηSL₂]`. Uses Shimura's
   Lemma 1.38 (CRT lifting for SL₂).
4. **Show ring homomorphism**: The map preserves multiplication. Follows from
   the existing `cosetMap_mulMap` machinery.
5. **Conclude isomorphism** by combining injectivity + surjectivity + ring hom.

### Phase D: Transfer the GL multiplication formula (~50 lines)

Use the isomorphism to transfer:
```
T_elem(![1, p]) * T_elem(![1, p^k]) = T_elem(![1, p^(k+1)]) + c_k • T_elem(![p, p^k])
```
(GL level, from `T_sum_prime_mul_T_ad`)

to:
```
T'(1, p) * T'(1, p^k) = T'(1, p^(k+1)) + c_k • T'(p, p^k)
```
(Gamma0 level, the helper lemma `Gamma0_T1p_mul_T1ppow_coprime`)

For this transfer, we need:
- `[1 0; 0 p^j] ∈ Delta_N_SL2` for all `j ≥ 0` (since first column is `[1, 0]`,
  trivially satisfies all mod-N conditions)
- `[p 0; 0 p^k] ∈ Delta_N_SL2` for `gcd(p, N) = 1` (first column `[p, 0]` reduces
  to a unit times `[1, 0]` in some appropriate equivalence)

(The exact details of which matrices are in `Delta_N` depends on the precise
definition; this is part of Phase A.)

### Phase E: Use the formula to fill the helper lemma sorry (~10 lines)

Apply Phase D's result to fill `Gamma0_T1p_mul_T1ppow_coprime`. Then the main
theorem `shimura_thm_3_35` is complete.

## Total Estimated Effort

- Phase A: ~30 lines (define `Delta_N_primitive`)
- Phase B: ~30 lines (define `Delta_N_SL2`)
- Phase C: ~150 lines (Prop 3.31 isomorphism)
- Phase D: ~50 lines (transfer the multiplication formula)
- Phase E: ~10 lines (use it)
- **Total: ~270 lines of new code**

This is the actual cost to finish Shimura 3.35 cleanly.

---

## Original Mathematical Strategy (Pre-Shimura Reading)

The approach I took before reading Shimura was to extract `T'(1, p^k)` from the
Hecke product `T'(1, p) * T'(1, p^{k-1})` at the Gamma0(N) level via the formula:

```
T'(1, p) * T'(1, p^{k-1}) = T'(1, p^k) + c_{k-1} • T'(p, p^{k-1})
```

where `c_{k-1} = p+1` if `k-1 = 1` (i.e., `k = 2`), and `c_{k-1} = p` if `k ≥ 3`.

This is the Gamma0-level analogue of Shimura's identity 3.24(5) (proved at GL
level as `T_sum_prime_mul_T_ad` in `GL2/MultiplicationTable.lean:487`).

This is exactly the same goal as Phase D above. Shimura's Prop 3.31 is the right
tool to prove it.

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
