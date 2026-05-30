# Hecke Ring: Shimura Theorem 3.24 Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove Shimura's Theorem 3.24 — the complete multiplication table for the Hecke ring R(Gamma, Delta) when n=2, including the ring structure on abstract Hecke rings.

**Architecture:** We already have a skeleton in `AbstractHeckeRing.lean` with definitions of `ArithmeticGroupPair`, double coset types `T'`, left coset types `M`, formal sums `T` and `M`, and partial ring/module instances. The plan fills all sorries bottom-up, then specializes to GL_2(Q)/SL_2(Z) and proves Theorem 3.24's seven identities.

**Tech Stack:** Lean 4, Mathlib (DoubleCoset, Commensurable, ConjAct, Finsupp, MonoidAlgebra patterns)

---

## Current Sorry Inventory (22 sorries)

| # | Location | Name/Description | Difficulty | Dependencies |
|---|----------|-----------------|------------|--------------|
| S1 | line 401 | `GG` — coset equality implies conjugate subgroup membership | Medium | None |
| S2 | line 511 | `rep_indep` — bijection construction | Medium | S1 |
| S3 | line 522 | `rep_indep` — final sorry | Medium | S2 |
| S4 | line 565 | `m'_T_one` backward direction | Medium | S2 |
| S5 | line 600 | `m'_one_T` backward direction | Medium | S4 |
| S6 | line 777 | `T_one_mul_singleton` sorry 1 | Medium | S5 |
| S7 | line 778 | `T_one_mul_singleton` sorry 2 | Medium | S5 |
| S8 | line 922 | `sum_single_eq_zero` partial | Easy | None |
| S9 | line 965 | `sum_single_support` | Easy | None |
| S10 | line 1354 | `sum_finset_single_indep3` partial | Medium | S8 |
| S11 | line 1382 | `T_eq_of_smul_single_eq_smul` | Hard | S10 |
| S12 | line 1411 | `T_single_smul_add` | Medium | None |
| S13 | line 1416 | `smul_add` | Medium | S12 |
| S14 | line 1432 | `T_eq_of_smul_eq_smul` support equality | Hard | S11, S13 |
| S15 | line 1441 | `T_eq_of_smul_eq_smul` final | Hard | S14 |
| S16 | line 1503 | `isScalarTower` | Hard | S12, S13 |
| S17 | line 1569 | `intCast` | Easy | None |
| S18 | line 1570 | `intCast_ofNat` | Easy | S17 |
| S19 | line 1571 | `intCast_negSucc` | Easy | S17 |
| S20-22 | line 659-671 | commented-out distributivity lemmas | Medium | N/A |

---

## Phase 0: Refactor — Split into Files

**Rationale:** The single 1580-line file is unwieldy. Split into focused modules for parallel work and maintainability.

### Task 0.1: Create file structure

**Files to create:**
- `LeanModularForms/HeckeRIngs/ArithmeticGroupPair.lean` — `ArithmeticGroupPair`, `T'`, `M`, constructors, basic lemmas (lines 1-310)
- `LeanModularForms/HeckeRIngs/Multiplicity.lean` — `m'`, `m`, `mm`, `mmm`, `rep_indep`, identity lemmas (lines 311-600)
- `LeanModularForms/HeckeRIngs/FinsuppLemmas.lean` — All the Finsupp manipulation lemmas (lines 857-1370)
- `LeanModularForms/HeckeRIngs/HeckeRing.lean` — `T`, `M`, ring instances, module action, faithfulness, associativity (lines 600-end)
- `LeanModularForms/HeckeRIngs/HeckeRingGL2.lean` — (later) Specialization to GL_2

**Decision point:** This refactor is optional. If you prefer to keep one file, skip to Phase 1. The plan works either way — all task references use lemma names, not line numbers.

---

## Phase 1: Core Group Theory Sorries (S1)

### Task 1.1: Prove `GG`

**File:** `AbstractHeckeRing.lean:386-401`

**Statement:** If `{h} * {d} * H = {h'} * {d} * H` then `(h')^{-1} * h` is in the conjugate subgroup `(ConjAct.toConjAct d • H).subgroupOf H`.

**Proof strategy:** The commented-out proof (lines 389-400) is 90% there. The key steps:
1. From `{h} * {d} * H = {h'} * {d} * H`, extract that `h * d` is in `{h'} * {d} * H`
2. So `h * d = h' * d * k` for some `k in H`
3. Then `h'^{-1} * h = d * k * d^{-1}` which is in `d H d^{-1} = ConjAct.toConjAct d • H`
4. Also `h'^{-1} * h in H` since both `h, h'` are in `H`
5. So `h'^{-1} * h in H ∩ (ConjAct d • H) = (ConjAct d • H).subgroupOf H`

**Key mathlib lemmas needed:**
- `Set.mem_mul` for extracting witnesses from `{h} * {d} * H`
- `Subgroup.mem_subgroupOf` for the intersection membership
- `ConjAct.smul_def`, `ConjAct.ofConjAct_toConjAct` for conjugation

**Step 1:** Uncomment the partial proof at lines 389-400 and fix it
**Step 2:** Build and verify: `lake build LeanModularForms.HeckeRIngs.AbstractHeckeRing`
**Step 3:** Commit

---

## Phase 2: Multiplicity Infrastructure (S2-S5)

### Task 2.1: Prove `rep_indep` (S2, S3)

**File:** `AbstractHeckeRing.lean:503-522`

**Statement:** `(mm P D1 D2 d).card = m' P Z D1 D2 d`

This asserts that the cardinality of the filtered finset equals the cardinality of the subtype. The proof needs a bijection between:
- `{(i,j) in Q(D1) x Q(D2) | i.out * D1.choose * j.out * D2.choose * H = d.choose * H}` (the subtype in `m'`)
- `(mm P D1 D2 d)` (the filtered finset in `mmm`)

**Proof strategy:**
1. Unfold `mm`, `mmm`, `m'`, `map1`
2. The bijection sends `(i,j)` to `T_mk P (i.out * D1.choose * j.out * D2.choose)`
3. Use `Nat.card_eq_of_bijective` or construct an explicit `Equiv`
4. The key fact is that `map1` sends `(i,j)` to the double coset containing that product

**Step 1:** Construct the explicit bijection
**Step 2:** Build and verify
**Step 3:** Commit

### Task 2.2: Prove `m'_T_one` backward direction (S4)

**File:** `AbstractHeckeRing.lean:564-565`

**Statement:** `m' P Z D1 (T_one P) d = 1 → D1 = d`

**Proof strategy:**
1. `m'` counts pairs `(i,j)` in `Q(D1) x Q(T_one)` with certain coset equality
2. Since `Q(T_one)` is a singleton (by `subsingleton_Q_T_one`), there's exactly one `j`
3. If the count is 1, there's exactly one valid `i`, which forces `D1 = d`
4. Use the uniqueness from `left_coset_exist_unique`

### Task 2.3: Prove `m'_one_T` backward direction (S5)

**File:** `AbstractHeckeRing.lean:589-600`

**Statement:** Similar to `m'_T_one` but for left multiplication by identity.

**Proof strategy:** Symmetric to Task 2.2, using the `Finset.card_eq_one` characterization already started at line 590.

---

## Phase 3: Ring Identity Sorries (S6-S7)

### Task 3.1: Prove `T_one_mul_singleton` (S6, S7)

**File:** `AbstractHeckeRing.lean:764-778`

**Statement:** `T_single P Z (T_one P) 1 * T_single P Z D2 b = T_single P Z D2 b`

**Proof strategy:** Mirror the proof of `T_singleton_one_mul` (lines 729-761) which is already complete. The key steps:
1. Reduce to showing `m P (T_one P) D2 = Finsupp.single D2 1` using `m'_one_T`
2. For `A = D2`: show the multiplicity is 1 using `m'_one_T`
3. For `A ≠ D2`: show the multiplicity is 0 by contradiction

**Dependency:** Tasks 2.2, 2.3

---

## Phase 4: Finsupp Helper Lemmas (S8-S10)

### Task 4.1: Prove `sum_single_eq_zero` case (S8)

**File:** `AbstractHeckeRing.lean:922`

**Statement:** In the induction step, if the sum is zero and we know the element, deduce `fs i = 0`.

**Proof strategy:** The proof is mostly done. The remaining sorry is in the `hl` branch where `h2 := h.2` and we need to connect the single element. Use `Finsupp.single_eq_zero` and the `eq_single_iff` characterization.

### Task 4.2: Prove `sum_single_support` (S9)

**File:** `AbstractHeckeRing.lean:958-965`

**Statement:** `(sum i in s, single i (fs i)).support ⊆ s`

**Proof strategy:**
1. Induction on `s`
2. Use `Finsupp.support_add` for the inductive step
3. Use `support_single_subset` for the base contribution
4. Chain with `Finset.union_subset_union`

The commented-out proof at lines 966-970 is almost correct — just needs the right `le_trans` chain.

### Task 4.3: Prove `sum_finset_single_indep3` partial (S10)

**File:** `AbstractHeckeRing.lean:1354`

**Proof strategy:** This is the case where `not all i in s ∩ t have x i = y i`. The proof should extract a witness `i` in `s ∩ t` with `x i ≠ y i`, then use the `d4` decomposition lemma to derive a contradiction or the desired conclusion.

---

## Phase 5: Module Action and Faithfulness (S11-S16)

This is the **critical phase** — it provides associativity.

### Task 5.1: Prove `T_single_smul_add` (S12)

**File:** `AbstractHeckeRing.lean:1404-1411`

**Statement:** `(T_single a c1 + T_single b c2) • m = T_single a c1 • m + T_single b c2 • m`

**Proof strategy:**
1. Unfold `T_smul_def` on both sides
2. Use `Finsupp.sum_add_index` for the left side
3. The key is showing the inner sums distribute correctly

### Task 5.2: Prove `smul_add` (S13)

**File:** `AbstractHeckeRing.lean:1413-1416`

**Statement:** Generalize `T_single_smul_add` to finite sums.

**Proof strategy:** Induction on `s` using `Finset.induction_on`, reducing to `T_single_smul_add` at each step.

### Task 5.3: Prove `T_eq_of_smul_single_eq_smul` (S11)

**File:** `AbstractHeckeRing.lean:1371-1382`

**Statement:** If `T_single T1 c1 • a = T_single T2 c2 • a` for all `a : M P Z`, then `T_single T1 c1 = T_single T2 c2`.

**Proof strategy:**
1. Specialize to `a = 1` (the identity in `M`)
2. Use `SFS_nonempty` to get nonempty support
3. Apply `sum_finset_single_indep2` or `sum_finset_single_indep3` to extract that `T1 = T2` and `c1 = c2` (or both zero)
4. This is the injectivity of the module map restricted to singletons

### Task 5.4: Prove `T_eq_of_smul_eq_smul` (S14, S15)

**File:** `AbstractHeckeRing.lean:1422-1441`

**Statement:** If `T1 • a = T2 • a` for all `a : M P Z`, then `T1 = T2`. (Full faithfulness.)

**Proof strategy:**
1. Write `T1 = sum of singletons` and `T2 = sum of singletons`
2. Use `smul_add` to distribute: `sum (T_single ...) • a = sum (T_single ... • a)`
3. Show supports must be equal (if they differ, specialize `a` to distinguish)
4. Show coefficients must be equal (using `T_eq_of_smul_single_eq_smul`)

### Task 5.5: Prove `isScalarTower` (S16)

**File:** `AbstractHeckeRing.lean:1503`

**Statement:** `IsScalarTower (T P Z) (T P Z) (M P Z)` — i.e., `(f * g) • m = f • (g • m)`.

**Proof strategy:**
1. Suffices to check on basis elements: `(T_single D1 a * T_single D2 b) • T_single m c = T_single D1 a • (T_single D2 b • T_single m c)`
2. Both sides expand to sums over `SFS P D1 ...` and `SFS P D2 m`
3. The key identity is that iterating left coset decompositions is the same as decomposing the product double coset — this follows from `DoubleCoset.doubleCoset_eq_iUnion_leftCosets` applied twice
4. This is the deepest proof in the whole development and corresponds to Shimura's Proposition 3.4

---

## Phase 6: Complete Ring Instance (S17-S19)

### Task 6.1: Fill `intCast` fields (S17-S19)

**File:** `AbstractHeckeRing.lean:1566-1571`

**Statement:** Define `intCast`, prove `intCast_ofNat`, `intCast_negSucc`.

**Proof strategy:**
```lean
intCast := fun n => T_single P Z (T_one P) (n : Z)
intCast_ofNat := fun n => by simp [one_def, T_single, Nat.cast_ofNat]
intCast_negSucc := fun n => by simp [one_def, T_single, Int.negSucc_eq]
```

This is straightforward once the additive group structure is in place.

### Task 6.2: Verify complete `Ring` instance

After all prior phases, the `Ring (T P Z)` instance at line 1573 should be sorry-free. Run:
```
lake build LeanModularForms.HeckeRIngs.AbstractHeckeRing
```
and verify zero `sorry` warnings.

---

## Phase 7: Specialize to GL_2(Q) / SL_2(Z)

This phase creates the concrete Hecke ring for modular forms.

### Task 7.1: Create `HeckeRingGL2.lean`

**File:** Create `LeanModularForms/HeckeRIngs/HeckeRingGL2.lean`

**Definitions needed:**

```lean
-- The group G = GL_2(Q) (invertible 2x2 rational matrices)
-- The subgroup Gamma = SL_2(Z)
-- The semigroup Delta = {alpha in M_2(Z) | det(alpha) > 0}

-- Concrete ArithmeticGroupPair
def GL2_pair : ArithmeticGroupPair (GL (Fin 2) Q) := {
  H := ...  -- SL_2(Z) as subgroup of GL_2(Q)
  Delta := ... -- positive determinant integral matrices
  h0 := ...  -- SL_2(Z) ≤ Delta
  h1 := ...  -- Delta ≤ commensurator(SL_2(Z))
}
```

**Key mathlib imports:**
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup`
- `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`

### Task 7.2: Define T(a,d) elements

Following Shimura Section 3.2:

```lean
-- T(a₁, ..., aₙ) = Gamma * diag[a₁,...,aₙ] * Gamma
-- For n=2: T(a,d) = Gamma * [[a,0],[0,d]] * Gamma

def T_ad (a d : Z) (ha : 0 < a) (hd : 0 < d) (had : a ∣ d) : T' GL2_pair := ...

-- T(m) = sum of all T(a,d) with ad = m, a | d
def T_m (m : Z) (hm : 0 < m) : T GL2_pair Z := ...
```

### Task 7.3: Prove `deg(T(a,d))` (Theorem 3.24, part 6)

**Statement:** `deg(T(p^i, p^{i+k})) = p^{k-1}(p+1)` for `k > 0`.

**Proof strategy:** By Proposition 3.18, `deg(T(a,d))` equals the number of k-dimensional subspaces of `(Z/pZ)^2`. Use the formula for Gaussian binomial coefficients.

### Task 7.4: Prove `deg(T(m))` (Theorem 3.24, part 7)

**Statement:** `deg(T(m)) = sigma_1(m)` (sum of positive divisors).

**Proof strategy:** By definition `T(m) = sum_{ad=m, a|d} T(a,d)`, and `deg(T(a,d)) = d/a * (something)`. Sum over divisors.

---

## Phase 8: Theorem 3.24 — The Multiplication Table

### Task 8.1: Prove identity (1): `T(m) = sum_{ad=m, a|d} T(a,d)`

This is **definitional** — it's just the definition of `T_m`.

### Task 8.2: Prove identity (2): `T(1, p^k) = T(p^k) - T(p,p) * T(p^{k-2})`

**Proof strategy:**
- Specialize Shimura's equation (5): `T(p)T(1, p^k) = T(1, p^{k+1}) + pT(p,p^k)` for k>1
- Use the recurrence to express T(1, p^k) in terms of T(p^k) and T(p,p)

### Task 8.3: Prove identity (3): `T(m)T(n) = sum_{d|(m,n)} d * T(d,d) * T(mn/d^2)`

**Proof strategy:** This is Shimura's main multiplication formula. The proof uses:
1. Express `T(m)` and `T(n)` as sums of `T(a,d)` elements
2. Use the product formula `T(a,d) * T(a',d') = ...` from the double coset multiplication
3. Collect terms

### Task 8.4: Prove identity (4): `T(p^r)T(p^s) = sum_{i=0}^r p^i T(p^i, p^i) T(p^{r+s-2i})`

**Proof strategy:** Specialize identity (3) to `m = p^r`, `n = p^s`. The divisors `d` of `gcd(p^r, p^s) = p^r` are exactly `p^0, p^1, ..., p^r`.

### Task 8.5: Prove identity (5): the recursion for `T(p)T(1, p^k)`

**Proof strategy:**
- For k=1: direct computation using the double coset decomposition
- For k>1: use identity (4) with r=1, s=k and simplify

---

## Dependency Graph

```
Phase 1 (GG)
    |
    v
Phase 2 (rep_indep, m'_T_one, m'_one_T)
    |
    v
Phase 3 (T_one_mul_singleton)         Phase 4 (Finsupp helpers)
    |                                       |
    v                                       v
    |                              Phase 5.1-5.2 (smul distributivity)
    |                                       |
    |                                       v
    |                              Phase 5.3-5.4 (faithfulness)
    |                                       |
    |                                       v
    |                              Phase 5.5 (isScalarTower)
    |                                       |
    v---------------------------------------v
                    |
                    v
            Phase 6 (Ring instance)
                    |
                    v
            Phase 7 (GL2 specialization)
                    |
                    v
            Phase 8 (Theorem 3.24)
```

**Note:** Phases 1-3 and Phase 4 are **independent** and can be worked in parallel.
Phase 6 (intCast) is also independent and can be done anytime.

---

## Priority Order for Maximum Impact

1. **Phase 1** (GG) — unlocks everything downstream
2. **Phase 6.1** (intCast) — easy win, independent
3. **Phase 4** (Finsupp helpers) — independent, unblocks faithfulness
4. **Phase 2** (multiplicity) — needs Phase 1
5. **Phase 3** (identity) — needs Phase 2
6. **Phase 5.1-5.2** (smul dist) — needs Phase 4
7. **Phase 5.3-5.5** (faithfulness + scalar tower) — the hard core
8. **Phase 7-8** (GL2 + Theorem 3.24) — the goal

---

## Estimated Sorry Count Per Phase

| Phase | Sorries Resolved | Remaining After |
|-------|-----------------|-----------------|
| 1 | 1 (S1) | 21 |
| 2 | 3 (S2-S4 + partial S5) | 18 |
| 3 | 2 (S6-S7) | 16 |
| 4 | 3 (S8-S10) | 13 |
| 5 | 5 (S11-S13, S14-S16) | 8 |
| 6 | 3 (S17-S19) | 5 |
| 7-8 | New code, new sorries then resolved | 0 |

---

## Alternative Approach: Rewrite Using MonoidAlgebra

Mathlib's `MonoidAlgebra R M` provides `Semiring`, `Ring`, etc. when `M` is a monoid and `R` is a (semi)ring. If we could make the set of double cosets `T' P` into a monoid (with multiplication being double coset product), then `T P Z = MonoidAlgebra Z (T' P)` would **automatically** inherit the ring structure.

**Pros:** Much less boilerplate; ring axioms come free from mathlib.
**Cons:** Making `T' P` a monoid requires proving associativity of double coset multiplication directly (rather than via module faithfulness). This is actually harder than the module approach.

**Recommendation:** Stick with the current Finsupp approach and the module faithfulness trick for associativity. This matches Shimura's proof structure.
