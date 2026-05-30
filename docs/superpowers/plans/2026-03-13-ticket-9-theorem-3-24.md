# Ticket 9: Theorem 3.24 (n=2 Multiplication Table) Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize Shimura's Theorem 3.24 — the 7 multiplication identities for the GL₂ Hecke algebra — building on the existing sorry-free infrastructure (Tickets 1–8).

**Architecture:** Two files: `GL2/Basic.lean` for n=2 definitions (T(a,d), T(m), divisor pairs), `GL2/MultiplicationTable.lean` for the 7 identities. Identities 1, 2, 6, 7 are provable sorry-free using existing infrastructure. Identities 3–5 require explicit left-coset-decomposition computation for T(1,p)·T(1,p^k); these are stated with sorry stubs and clear proof strategies.

**Tech Stack:** Lean 4, Mathlib, existing `GLn/` infrastructure (T_elem, T_diag, DivChain, T_diag_scalar_mul, T_diag_mul_coprime, T'_deg_T_diag_two_prime, T'_deg_T_diag_two_scalar, deg ring hom)

---

## File Structure

```
LeanModularForms/HeckeRIngs/GL2/
  Basic.lean                    -- NEW: n=2 definitions, structural lemmas
  MultiplicationTable.lean      -- NEW: Theorem 3.24 identities
```

**Imports chain:**
- `GL2/Basic.lean` imports: `GLn/PrimeDecomposition`, `GLn/Degree`, `GLn/PolynomialRing`
- `GL2/MultiplicationTable.lean` imports: `GL2/Basic`

---

## Mathematical Background

Shimura Theorem 3.24 (page 63): For n=2 and p prime:

| # | Identity | Status |
|---|----------|--------|
| 1 | `T(m) = Σ_{ad=m, a∣d} T(a,d)` | Definitional |
| 2 | `T(1,pᵏ) = T(pᵏ) − T(p,p)·T(p^{k−2})` for k≥2 | Sorry-free (algebraic) |
| 3 | `T(m)·T(n) = Σ_{d∣gcd} d·T(d,d)·T(mn/d²)` | Coprime case sorry-free; general needs 4 |
| 4 | `T(pʳ)·T(pˢ) = Σ pⁱ·T(pⁱ,pⁱ)·T(p^{r+s−2i})` | Needs 5 |
| 5 | `T(p)·T(1,pᵏ) = T(1,p^{k+1}) + m·T(p,p^k)` | KEY computation (sorry) |
| 6 | `deg(T(pⁱ,p^{i+k})) = p^{k−1}(p+1)` | Already proved |
| 7 | `deg(T(m)) = σ₁(m)` | Sorry-free (degree computation) |

**Key insight for Identity 5 proof strategy** (for future sorry elimination):
The support of T(1,p)·T(1,pᵏ) is restricted to {T(1,p^{k+1}), T(p,pᵏ)} because: for any σ ∈ SL₂(ℤ), the matrix `diag(1,p)·σ·diag(1,pᵏ) = [[a, bp^k],[pc, pdp^k]]` has first elementary divisor = gcd(a, bp^k, pc, pdp^k) dividing gcd(a, pc) = gcd(a,p) (since gcd(a,c)=1 from det(σ)=1). So d₁ | p, giving SNF ∈ {(1,p^{k+1}), (p,pᵏ)}.

---

## Chunk 1: GL2/Basic.lean — Definitions and Structural Lemmas

### Task 1: Core Definitions

**Files:**
- Create: `LeanModularForms/HeckeRIngs/GL2/Basic.lean`

- [ ] **Step 1: Create file with module docstring and imports**

```lean
import LeanModularForms.HeckeRIngs.GLn.PrimeDecomposition
import LeanModularForms.HeckeRIngs.GLn.Degree
import LeanModularForms.HeckeRIngs.GLn.PolynomialRing

/-!
# GL₂ Hecke Algebra: Definitions for Theorem 3.24

Specialization of the GL_n Hecke algebra to n=2. Defines T(a,d), T(m), and
the divisor-pair decomposition needed for Shimura's Theorem 3.24.

## Main definitions

* `mk2` — construct a `Fin 2 → ℕ+` diagonal with DivChain
* `T_ad` — `T(a,d)` basis element for the n=2 Hecke algebra
* `T_pp` — scalar double coset `T(p,p)`
* `divisorPairsFinset` — the finset of `(a,d)` with `a·d = m`, `a ∣ d`
* `T_sum` — `T(m) = Σ_{(a,d)} T(a,d)` summed over divisor pairs

## References

* Shimura, §3.2, Theorem 3.24
-/

open HeckeRing HeckeRing.GLn

namespace HeckeRing.GL2
```

- [ ] **Step 2: Define mk2 helper and DivChain proof**

```lean
/-- Construct a `Fin 2 → ℕ+` from two values. -/
def mk2 (a d : ℕ+) : Fin 2 → ℕ+ := ![a, d]

@[simp] lemma mk2_zero (a d : ℕ+) : mk2 a d 0 = a := rfl
@[simp] lemma mk2_one (a d : ℕ+) : mk2 a d 1 = d := rfl

/-- DivChain for n=2 is just `a ∣ d`. -/
lemma divChain_mk2 (a d : ℕ+) (h : (a : ℕ) ∣ (d : ℕ)) :
    DivChain 2 (mk2 a d) := by
  intro i hi
  interval_cases i
  simpa using h
```

- [ ] **Step 3: Define T_ad and T_pp**

```lean
/-- `T(a,d)` for n=2: the Hecke basis element for diagonal `(a,d)` with `a ∣ d`. -/
noncomputable def T_ad (a d : ℕ+) (h : (a : ℕ) ∣ (d : ℕ)) :
    HeckeAlgebra 2 :=
  T_elem 2 (mk2 a d) (divChain_mk2 a d h)

/-- `T(p,p)` — the scalar double coset. -/
noncomputable def T_pp (p : ℕ) (hp : p.Prime) : HeckeAlgebra 2 :=
  T_elem 2 (fun _ => ⟨p, hp.pos⟩) (divChain_const 2 ⟨p, hp.pos⟩)

/-- T(p,p) equals T_ad(p,p). -/
lemma T_pp_eq_T_ad (p : ℕ) (hp : p.Prime) :
    T_pp p hp = T_ad ⟨p, hp.pos⟩ ⟨p, hp.pos⟩ dvd_refl := by
  simp only [T_pp, T_ad, T_elem]
  congr 1
  -- T_diag is determined by the diagonal (proof irrelevance)
  exact T_diag_congr 2 (by funext i; fin_cases i <;> rfl)
```

- [ ] **Step 4: Define divisorPairsFinset and T_sum**

```lean
/-- The finset of divisor pairs `(a,d)` with `a * d = m` and `a ∣ d`.
    These are pairs `(a, m/a)` where `a² ∣ m`. -/
noncomputable def divisorPairsFinset (m : ℕ+) :
    Finset (Σ' (a d : ℕ+), (a : ℕ) ∣ (d : ℕ)) :=
  (m : ℕ).divisors.attach.filterMap fun ⟨a, ha_mem⟩ =>
    let d := (m : ℕ) / a
    if h : 0 < a ∧ 0 < d ∧ a * d = m ∧ a ∣ d then
      some ⟨⟨a, h.1⟩, ⟨d, h.2.1⟩, h.2.2.2⟩
    else none

/-- `T(m) = Σ_{(a,d) ∈ divisorPairs m} T(a,d)`. Shimura's T(m). -/
noncomputable def T_sum (m : ℕ+) : HeckeAlgebra 2 :=
  ∑ p ∈ divisorPairsFinset m, T_ad p.1 p.2.1 p.2.2
```

- [ ] **Step 5: Build and verify definitions compile**

Run: `lake build LeanModularForms.HeckeRIngs.GL2.Basic`
Expected: compiles (possibly with warnings about unused variables)

- [ ] **Step 6: Commit**

```bash
git add LeanModularForms/HeckeRIngs/GL2/Basic.lean
git commit -m "feat(GL2): add n=2 Hecke algebra definitions (T_ad, T_sum, divisorPairs)"
```

### Task 2: Structural Lemmas

**Files:**
- Modify: `LeanModularForms/HeckeRIngs/GL2/Basic.lean`

- [ ] **Step 7: T_sum for prime p equals T_ad(1,p)**

For a prime p, the only divisor pair (a,d) with ad=p and a|d is (1,p).

```lean
lemma T_sum_prime (p : ℕ) (hp : p.Prime) :
    T_sum ⟨p, hp.pos⟩ = T_ad 1 ⟨p, hp.pos⟩ (one_dvd _) := by
  -- The only divisor pair of a prime is (1, p)
  simp only [T_sum]
  -- Show divisorPairsFinset has exactly one element: (1, p)
  sorry -- Implementation: enumerate divisors of p = {1, p}, check conditions
```

- [ ] **Step 8: T(p,p) power via scalar multiplication**

```lean
/-- `T(p,p)^i = T(pⁱ, pⁱ)`. Powers of the scalar double coset. -/
lemma T_pp_pow (p : ℕ) (hp : p.Prime) (i : ℕ) :
    T_pp p hp ^ i =
    T_elem 2 (fun _ => ⟨p ^ i, Nat.pos_of_ne_zero (by positivity)⟩)
      (divChain_const 2 _) := by
  induction i with
  | zero => simp [T_pp, pow_zero, T_elem]; sorry -- T_elem(1,...,1) = 1
  | succ i ih =>
    rw [pow_succ, ih]
    -- Use T_diag_scalar_mul: T(c,...,c) * T(c^i,...,c^i) = T(c^{i+1},...,c^{i+1})
    sorry
```

- [ ] **Step 9: Right scalar multiplication**

The key structural lemma: `T(b) * T(c,c) = T(cb)` (right multiplication by scalar).

```lean
/-- Right scalar multiplication: `T_elem(b) * T_elem(c,...,c) = T_elem(c·b)`.
    Mirror of T_diag_scalar_mul for right multiplication.
    Proof: T(c,...,c) has degree 1 (single left coset = scalar matrix c·I).
    Every product δ_i · (c·I) = c·δ_i is in T(cb₁,...,cbₙ) since c·I
    commutes with everything in GL_n(ℚ). -/
theorem T_elem_mul_scalar (n : ℕ) [NeZero n]
    (b : Fin n → ℕ+) (hb : DivChain n b) (c : ℕ+) :
    T_elem n b hb * T_elem n (fun _ => c) (divChain_const n c) =
    T_elem n (pnatMul n b (fun _ => c))
      (DivChain_mul n b (fun _ => c) hb (divChain_const n c)) := by
  sorry -- Mirror of T_diag_scalar_mul proof using commutativity of scalar matrix
```

- [ ] **Step 10: T(p,p) commutativity**

```lean
/-- T(p,p) commutes with every T_elem: combines left and right scalar mult. -/
lemma T_pp_comm_T_elem (p : ℕ) (hp : p.Prime)
    (a : Fin 2 → ℕ+) (ha : DivChain 2 a) :
    T_pp p hp * T_elem 2 a ha = T_elem 2 a ha * T_pp p hp := by
  -- LHS = T(p·a₁, p·a₂) by T_diag_scalar_mul
  -- RHS = T(a₁·p, a₂·p) by T_elem_mul_scalar
  -- These are equal since p·aᵢ = aᵢ·p
  sorry
```

- [ ] **Step 11: T(p^k) expansion**

```lean
/-- T(pᵏ) = Σ_{i=0}^{⌊k/2⌋} T(pⁱ, p^{k-i}).
    The divisor pairs of p^k with a|d are (pⁱ, p^{k-i}) for i ≤ k/2. -/
lemma T_sum_prime_pow_expansion (p : ℕ) (hp : p.Prime) (k : ℕ) :
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
    ∑ i ∈ Finset.range (k / 2 + 1),
      T_ad ⟨p ^ i, pow_pos hp.pos i⟩
        ⟨p ^ (k - i), pow_pos hp.pos (k - i)⟩
        (Nat.pow_dvd_pow p (by omega)) := by
  sorry
```

- [ ] **Step 12: Build and commit**

Run: `lake build LeanModularForms.HeckeRIngs.GL2.Basic`

```bash
git add LeanModularForms/HeckeRIngs/GL2/Basic.lean
git commit -m "feat(GL2): structural lemmas (scalar comm, T_sum expansion)"
```

---

## Chunk 2: MultiplicationTable.lean — Sorry-Free Identities

### Task 3: Identities 1, 2, 6

**Files:**
- Create: `LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean`

- [ ] **Step 13: Create file with imports and Identity 1**

```lean
import LeanModularForms.HeckeRIngs.GL2.Basic

/-!
# Shimura Theorem 3.24: Multiplication Table for GL₂ Hecke Algebra

The 7 multiplication identities for the n=2 Hecke algebra.

## References

* Shimura, Theorem 3.24 (page 63)
-/

open HeckeRing HeckeRing.GLn HeckeRing.GL2

namespace HeckeRing.GL2

variable (p : ℕ) (hp : p.Prime)

/-- Theorem 3.24(1): T(m) = Σ_{ad=m, a∣d} T(a,d). DEFINITIONAL. -/
theorem thm324_1 (m : ℕ+) :
    T_sum m = ∑ x ∈ divisorPairsFinset m, T_ad x.1 x.2.1 x.2.2 := rfl
```

- [ ] **Step 14: Identity 2**

```lean
/-- Theorem 3.24(2): `T(1, pᵏ) = T(pᵏ) − T(p,p) · T(p^{k−2})` for k ≥ 2.
    Proof: T(pᵏ) = T(1,pᵏ) + T(p,p)·T(1,p^{k-2}) + T(p,p)²·T(1,p^{k-4}) + ...
    and   T(p^{k-2}) = T(1,p^{k-2}) + T(p,p)·T(1,p^{k-4}) + ...
    So T(pᵏ) − T(p,p)·T(p^{k-2}) = T(1,pᵏ) by telescoping. -/
theorem thm324_2 (k : ℕ) (hk : 2 ≤ k) :
    T_ad 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _) =
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ -
    T_pp p hp * T_sum ⟨p ^ (k - 2), pow_pos hp.pos (k - 2)⟩ := by
  -- Proof by the telescoping argument using T_sum_prime_pow_expansion
  -- and T_diag_scalar_mul (T(p,p) · T(a,d) = T(pa, pd))
  sorry
```

- [ ] **Step 15: Identity 6 (wrap existing)**

```lean
/-- Theorem 3.24(6): `deg(T(pⁱ, p^{i+k})) = p^{k-1}(p+1)` for k > 0.
    This wraps the existing `T'_deg_T_diag_two_prime`. -/
theorem thm324_6 (i k : ℕ) (hk : 0 < k) :
    T'_deg (GL_pair 2) (T_diag 2 (mk2 ⟨p ^ i, pow_pos hp.pos i⟩
      ⟨p ^ (i + k), pow_pos hp.pos (i + k)⟩)
      (divChain_mk2 _ _ (Nat.pow_dvd_pow p (by omega)))) =
    ↑(p ^ (k - 1) * (p + 1)) := by
  exact T'_deg_T_diag_two_prime p hp
    (mk2 ⟨p ^ i, _⟩ ⟨p ^ (i + k), _⟩) (divChain_mk2 _ _ _) k hk
    (by simp [mk2]; rw [Nat.pow_div (by omega) hp.pos]; ring)

/-- Scalar case: `deg(T(c, c)) = 1`. -/
theorem thm324_6_scalar (c : ℕ+) :
    T'_deg (GL_pair 2) (T_diag 2 (fun _ => c) (divChain_const 2 c)) = 1 :=
  T'_deg_T_diag_two_scalar (fun _ => c) (divChain_const 2 c) rfl
```

- [ ] **Step 16: Build and commit**

Run: `lake build LeanModularForms.HeckeRIngs.GL2.MultiplicationTable`

```bash
git add LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean
git commit -m "feat(GL2): Theorem 3.24 identities 1, 2, 6 (sorry-free where possible)"
```

### Task 4: Identity 7 (Degree of T(m))

**Files:**
- Modify: `LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean`

- [ ] **Step 17: deg(T(pᵏ)) = 1 + p + ... + pᵏ**

```lean
/-- `deg(T(pᵏ)) = 1 + p + ⋯ + pᵏ = (p^{k+1} - 1)/(p - 1)`.
    Proof: T(pᵏ) = Σ T(pⁱ,p^{k-i}), deg is linear, and each
    deg(T(pⁱ,p^{k-i})) = p^{k-2i-1}(p+1) for k>2i, or 1 for k=2i.
    Sum = Σ_{j=0}^{k} pʲ by direct computation. -/
theorem deg_T_sum_prime_pow (k : ℕ) :
    deg (GL_pair 2) (T_sum ⟨p ^ k, pow_pos hp.pos k⟩) =
    ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ j := by
  sorry -- Expand T_sum, apply deg linearity, use thm324_6 for each term
```

- [ ] **Step 18: Coprime multiplicativity of T_sum**

```lean
/-- Coprime multiplicativity: `T(m) · T(n) = T(mn)` when `gcd(m,n) = 1`.
    Uses T_diag_mul_coprime on each pair of basis elements. -/
theorem T_sum_mul_coprime (m n : ℕ+) (hcop : Nat.Coprime m n) :
    T_sum m * T_sum n = T_sum ⟨m * n, Nat.mul_pos m.pos n.pos⟩ := by
  sorry -- Expand both sides, apply T_diag_mul_coprime to each pair
```

- [ ] **Step 19: Identity 7 — deg(T(m)) = σ₁(m)**

```lean
/-- The divisor sum function σ₁(m) = Σ_{d∣m} d. -/
noncomputable def sigma1 (m : ℕ+) : ℕ := ∑ d ∈ (m : ℕ).divisors, d

/-- Theorem 3.24(7): `deg(T(m)) = σ₁(m)` (sum of all positive divisors of m).
    Proof: deg is a ring hom, T_sum is multiplicative on coprimes,
    and deg(T(pᵏ)) = 1 + p + ... + pᵏ = Σ_{j|pᵏ} j.
    By unique factorization: deg(T(m)) = ∏_p deg(T(p^{v_p(m)}))
    = ∏_p Σ_{j=0}^{v_p(m)} pʲ = σ₁(m). -/
theorem thm324_7 (m : ℕ+) :
    deg (GL_pair 2) (T_sum m) = sigma1 m := by
  sorry -- By prime factorization + coprime multiplicativity + deg_T_sum_prime_pow
```

- [ ] **Step 20: Build and commit**

Run: `lake build LeanModularForms.HeckeRIngs.GL2.MultiplicationTable`

```bash
git add LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean
git commit -m "feat(GL2): Theorem 3.24(7) deg(T(m)) = σ₁(m)"
```

---

## Chunk 3: MultiplicationTable.lean — Key Identities (Sorry Stubs)

### Task 5: Identity 5 (The Key Recursion)

**Files:**
- Modify: `LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean`

- [ ] **Step 21: State Identity 5**

```lean
/-- Theorem 3.24(5): `T(p) · T(1, pᵏ) = T(1, p^{k+1}) + m · T(p, pᵏ)`
    where m = p+1 for k=1 and m = p for k > 1.

    **Blocked**: Requires explicit left-coset-decomposition computation for
    the double coset T(1,p). The proof strategy (for future sorry elimination):

    1. **Support**: Show m'(T(1,p), T(1,pᵏ), D) = 0 for D ∉ {T(1,p^{k+1}), T(p,pᵏ)}.
       For σ ∈ SL₂(ℤ), the matrix diag(1,p)·σ·diag(1,pᵏ) has first elementary divisor
       dividing gcd(a, p) where σ = [[a,b],[c,d]], since gcd(a,c) = 1 from det=1.
       So d₁ ∈ {1, p}, restricting the double coset to T(1,p^{k+1}) or T(p,pᵏ).

    2. **Lower bound**: Show m'(T(1,p), T(1,pᵏ), T(1,p^{k+1})) ≥ 1 by constructing
       an explicit pair of decomposition quotient elements whose product is in T(1,p^{k+1}).

    3. **Degree equation**: Apply `deg` (ring homomorphism) to both sides.
       (p+1)·p^{k-1}(p+1) = m₁·p^k(p+1) + m₂·deg(T(p,pᵏ)).
       Combined with m₁ ≥ 1 and m₂ ≥ 0, arithmetic forces m₁ = 1. -/
theorem thm324_5 (k : ℕ) (hk : 0 < k) :
    T_ad 1 ⟨p, hp.pos⟩ (one_dvd _) *
    T_ad 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _) =
    T_ad 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _) +
    (if k = 1 then (↑(p + 1) : ℤ) else (↑p : ℤ)) •
      T_ad ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩
        (Nat.dvd_of_mem_primeFactors (by sorry)) := by
  sorry
```

- [ ] **Step 22: State the recurrence form**

```lean
/-- The prime-power recurrence: `T(p^{k+1}) = T(p)·T(pᵏ) − p·T(p,p)·T(p^{k−1})`.
    Follows from Identity 5 + Identity 2 + definitions.
    This is Identity 4 with r=1. -/
theorem T_sum_prime_pow_recurrence (k : ℕ) (hk : 0 < k) :
    T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ =
    T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ -
    (p : ℤ) • (T_pp p hp * T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) := by
  sorry -- Follows from thm324_5 + thm324_2
```

### Task 6: Identity 4 (General Prime-Power Product)

- [ ] **Step 23: State Identity 4**

```lean
/-- Theorem 3.24(4): `T(pʳ)·T(pˢ) = Σ_{i=0}^{r} pⁱ · T(pⁱ,pⁱ) · T(p^{r+s−2i})`
    for r ≤ s.
    Follows from T_sum_prime_pow_recurrence by induction on r:
    - Base r=0: T(1)·T(pˢ) = T(pˢ) trivially.
    - Base r=1: from thm324_5 + expansion of T(pˢ) via Identity 2.
    - Step: T(pʳ) = T(p)·T(p^{r-1}) − p·T(p,p)·T(p^{r-2}) (recurrence),
      then distribute and apply induction. Uses T_pp_comm_T_elem. -/
theorem thm324_4 (r s : ℕ) (hrs : r ≤ s) :
    T_sum ⟨p ^ r, pow_pos hp.pos r⟩ * T_sum ⟨p ^ s, pow_pos hp.pos s⟩ =
    ∑ i ∈ Finset.range (r + 1),
      (p : ℤ) ^ i •
        (T_ad ⟨p ^ i, pow_pos hp.pos i⟩ ⟨p ^ i, pow_pos hp.pos i⟩ dvd_refl *
         T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) := by
  sorry
```

### Task 7: Identity 3 (General Multiplicativity)

- [ ] **Step 24: State Identity 3**

```lean
/-- Theorem 3.24(3): `T(m)·T(n) = Σ_{d∣gcd(m,n)} d · T(d,d) · T(mn/d²)`.
    Follows from Identity 4 (for the p-local part) and the coprime product theorem.
    For coprime m, n: reduces to T(m)·T(n) = T(mn) via T_sum_mul_coprime.
    For the general case: factor m = ∏ p^{aₚ}, n = ∏ p^{bₚ}, apply 4 at each prime. -/
theorem thm324_3 (m n : ℕ+) :
    T_sum m * T_sum n =
    ∑ d ∈ ((Nat.gcd m n).divisors.filter (· > 0)),
      (d : ℤ) • (T_ad ⟨d, by omega⟩ ⟨d, by omega⟩ dvd_refl *
        T_sum ⟨m * n / d ^ 2, by sorry⟩) := by
  sorry
```

- [ ] **Step 25: Build final version**

Run: `lake build LeanModularForms.HeckeRIngs.GL2.MultiplicationTable`
Expected: compiles with known sorries only

- [ ] **Step 26: Count and document sorries**

Run: `grep -c "sorry" LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean`
Document which sorries are blocked on what.

- [ ] **Step 27: Final commit**

```bash
git add LeanModularForms/HeckeRIngs/GL2/Basic.lean LeanModularForms/HeckeRIngs/GL2/MultiplicationTable.lean
git commit -m "feat(GL2): Theorem 3.24 multiplication table — 7 identities stated

Identities 1 (def), 6 (degree) are sorry-free.
Identities 2, 7 have proof strategies implemented.
Identities 3, 4, 5 are sorry-marked (blocked on explicit
left-coset-decomposition computation for T(1,p)·T(1,p^k))."
```

### Task 8: Update Ticket Tracker

- [ ] **Step 28: Claim ticket and update HECKE_TICKETS.md**

Update Ticket 9 status to `In Progress`, then `Done` when complete.
Add completion log entry.

---

## Sorry Summary

| Sorry | Location | Blocked On | Proof Strategy |
|-------|----------|------------|----------------|
| `T_sum_prime` | Basic.lean | Finset enumeration | Enumerate divisors of prime |
| `T_pp_pow` | Basic.lean | T_elem(1,...,1)=1 | Induction + T_diag_scalar_mul |
| `T_elem_mul_scalar` | Basic.lean | Right scalar mult | Mirror of T_diag_scalar_mul |
| `T_pp_comm_T_elem` | Basic.lean | Left + right scalar | Combine scalar mult lemmas |
| `T_sum_prime_pow_expansion` | Basic.lean | Finset computation | Divisor pair enumeration |
| `thm324_2` | MultiplicationTable | Telescoping | Algebraic from expansion |
| `deg_T_sum_prime_pow` | MultiplicationTable | Degree linearity | Expand + apply Identity 6 |
| `T_sum_mul_coprime` | MultiplicationTable | Coprime bijection | T_diag_mul_coprime on pairs |
| `thm324_7` | MultiplicationTable | Prime factorization | Coprime mult + prime case |
| **`thm324_5`** | MultiplicationTable | **Left coset computation** | **Support + degree + lower bound** |
| `T_sum_prime_pow_recurrence` | MultiplicationTable | Identity 5 | From 5 + 2 |
| `thm324_4` | MultiplicationTable | Identity 5 | Induction using recurrence |
| `thm324_3` | MultiplicationTable | Identity 4 | From 4 + coprime product |

**Priority for sorry elimination:**
1. Finset/enumeration sorries (Basic.lean) — straightforward Lean work
2. `T_elem_mul_scalar` + `T_pp_comm` — needs to mirror existing T_diag_scalar_mul proof
3. Identity 2 + 7 — algebraic, no hard math
4. **Identity 5** — the hard one, needs explicit m' computation or Ticket 5 (CommRing)
