# E4-E6 Generators Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the graded ring of level 1 modular forms is isomorphic to the weighted polynomial ring in E4 and E6: `MvPolynomial (Fin 2) C ~=_alg bigoplus_k M_k(Gamma(1))`.

**Architecture:** Define an evaluation AlgHom from MvPolynomial via `MvPolynomial.aeval`, prove surjectivity by strong induction on weight (using cusp form decomposition via Delta), then prove injectivity by dimension counting (parallel recurrence argument). The key existing infrastructure: `CuspForms_iso_Modforms`, `IsCuspForm_iff_coeffZero_eq_zero`, `Delta_E4_eqn`, `dim_modforms_eq_one_add_dim_cuspforms`.

**Tech Stack:** Lean 4 + Mathlib (`MvPolynomial`, `DirectSum`, `GradedAlgebra`), project files `Eisenstein.lean`, `DimensionFormulas.lean`, `IsCuspForm.lean`

**Spec:** `docs/superpowers/specs/2026-03-31-E4-E6-generators-design.md`

---

### Task 1: File Skeleton and Core Definitions

**Files:**
- Create: `LeanModularForms/Modularforms/Generators.lean`

- [ ] **Step 1: Create file with imports and core definitions**

```lean
module

import LeanModularForms.Modularforms.DimensionFormulas
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup DirectSum

noncomputable section

/-- Weight function assigning weight 4 to X₀ and weight 6 to X₁. -/
def E₄E₆Weight : Fin 2 → ℕ := ![4, 6]

/-- Evaluation homomorphism sending X₀ ↦ E₄ and X₁ ↦ E₆ in the graded ring. -/
def evalE₄E₆ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ⨁ k : ℤ, ModularForm Γ(1) k :=
  MvPolynomial.aeval ![DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 4 E₄,
                        DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 6 E₆]

/-- The polynomial (X₀³ - X₁²) / 1728 representing Delta. -/
def Delta_poly : MvPolynomial (Fin 2) ℂ :=
  (1 / 1728 : ℂ) • (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)
```

- [ ] **Step 2: Build to verify definitions compile**

Run: `lake build LeanModularForms.Modularforms.Generators`

If there are import issues (e.g., `MvPolynomial` needs `import Mathlib.RingTheory.MvPolynomial.Basic`), fix imports. The `DirectSum.GAlgebra` instance for `ModularForm` is needed for `MvPolynomial.aeval` — it comes from `Mathlib.NumberTheory.ModularForms.Basic` (transitively imported via `Eisenstein.lean`). Verify the `Algebra ℂ (⨁ k : ℤ, ModularForm Γ(1) k)` instance resolves. You may need `HasDetOne` or `HasDetPlusMinusOne` instances — check what's needed and add appropriate instance assumptions or use `Gamma 1` specific instances.

**Critical:** If `MvPolynomial.aeval` doesn't typecheck because the target algebra instance isn't found, you may need to help Lean find it. Try explicit type annotations or `@MvPolynomial.aeval` with explicit arguments. The existing code in `DimensionFormulas.lean:614-616` shows how `DirectSum.of _ 4 E₄` is used in practice.

- [ ] **Step 3: Commit**

```bash
git add LeanModularForms/Modularforms/Generators.lean
git commit -m "feat: add E4-E6 generators file skeleton with evalE₄E₆ definition"
```

---

### Task 2: Odd Weight Vanishing

We need `M_k(Gamma(1)) = 0` for odd k. This is not in the existing codebase or mathlib.

**Files:**
- Modify: `LeanModularForms/Modularforms/Generators.lean`

- [ ] **Step 1: State and prove odd weight vanishing**

The proof uses: `-I ∈ Gamma(1)`, and the slash action of `-I` on weight k gives `(-1)^k * f`, so for odd k, `f = -f`, hence `f = 0`.

```lean
/-- In level 1, modular forms of odd weight are zero. -/
lemma levelOne_odd_weight_eq_zero {k : ℤ} (hk : Odd k) (f : ModularForm Γ(1) k) : f = 0 := by
  sorry
```

**Proof strategy:** Use `f.slash_action_eq'` with `γ = -1 : SL(2, ℤ)` to get `f |_k (-I) = f`. Then compute `f |_k (-I) = (-1)^k * f` using `SL_slash_apply` and the fact that `ModularGroup.denom` of `-I` is `-1`. For odd k, `(-1)^k = -1`, giving `f = -f`, hence `2 * f = 0`, hence `f = 0` (ℂ has char 0).

You may need:
- `-1 ∈ Gamma 1` (or `CongruenceSubgroup.mem_Gamma_one`)
- `SL_slash_apply` for the slash action formula
- `(-I) • z = z` (the Mobius action of -I is trivial)
- `zpow_neg_one` or `neg_one_zpow_odd` for `(-1)^k = -1` when k is odd

- [ ] **Step 2: Build to verify**

Run: `lake build LeanModularForms.Modularforms.Generators`
Expected: Builds (with sorry warning if not yet filled, or clean if filled).

- [ ] **Step 3: Derive rank-zero corollary**

```lean
lemma levelOne_odd_weight_rank_zero {k : ℤ} (hk : Odd k) :
    Module.rank ℂ (ModularForm Γ(1) k) = 0 := by
  rw [rank_zero_iff_forall_zero]
  exact fun f => levelOne_odd_weight_eq_zero hk f
```

- [ ] **Step 4: Build and commit**

Run: `lake build LeanModularForms.Modularforms.Generators`

```bash
git add LeanModularForms/Modularforms/Generators.lean
git commit -m "feat(Generators): odd weight vanishing for level 1 modular forms"
```

---

### Task 3: Combinatorial Helpers

**Files:**
- Modify: `LeanModularForms/Modularforms/Generators.lean`

- [ ] **Step 1: Monomial existence for even weights >= 4**

```lean
/-- For even k >= 4, there exist a, b in N with 4a + 6b = k. -/
lemma monomial_weight_exists (k : ℕ) (hk : 4 ≤ k) (hkeven : Even k) :
    ∃ a b : ℕ, 4 * a + 6 * b = k := by
  sorry
```

**Proof strategy:** Case split on `k % 6`:
- `k ≡ 0 mod 6`: `a = 0, b = k/6`
- `k ≡ 2 mod 6`: `a = 2, b = (k-8)/6` (need `k ≥ 8`; for `k = 2` not reachable since `4 ≤ k`)
- `k ≡ 4 mod 6`: `a = 1, b = (k-4)/6`

Since k is even, `k % 6 ∈ {0, 2, 4}`. Use `omega` to close arithmetic goals after the case split. Consider using `Nat.even_iff` and a modular arithmetic case split, or just handle small cases `k ∈ {4,6,8,10}` by `decide`/`omega` and prove the recurrence `(a, b) → (a+3, b)` maps solutions for `k-12` to solutions for `k`.

- [ ] **Step 2: Unique small-a solution for k >= 8 even**

```lean
/-- For even k >= 8, exactly one solution (a,b) to 4a+6b=k has a < 3. -/
lemma monomial_small_a_unique (k : ℕ) (hk : 8 ≤ k) (hkeven : Even k) :
    ∃! ab : ℕ × ℕ, ab.1 < 3 ∧ 4 * ab.1 + 6 * ab.2 = k := by
  sorry
```

**Proof strategy:** Same case split on `k % 6`. For each residue class, exhibit the unique solution and show no other `a < 3` works (by `omega` on the constraints).

- [ ] **Step 3: Monomial count recurrence**

```lean
/-- The number of monomials of weight k equals 1 + the number of weight k-12,
    for even k >= 12. This is the key for the dimension counting argument. -/
lemma monomial_count_step (k : ℕ) (hk : 12 ≤ k) (hkeven : Even k) :
    Finset.card (Finset.filter (fun ab : ℕ × ℕ => 4 * ab.1 + 6 * ab.2 = k)
      (Finset.range (k+1) ×ˢ Finset.range (k+1))) =
    1 + Finset.card (Finset.filter (fun ab : ℕ × ℕ => 4 * ab.1 + 6 * ab.2 = k - 12)
      (Finset.range (k+1) ×ˢ Finset.range (k+1))) := by
  sorry
```

**Proof strategy:** Use the bijection `(a, b) ↦ (a + 3, b)` from solutions of `4a+6b = k-12` to solutions of `4a+6b = k` with `a >= 3`, plus `monomial_small_a_unique` for the extra solution with `a < 3`. This involves `Finset.card_filter` manipulations: split the filter set into `{a ≥ 3}` and `{a < 3}`, show the first part bijects with the k-12 solutions, the second has cardinality 1.

Alternatively, if this Finset approach is cumbersome, define the count as a function `monomialCount : ℕ → ℕ` recursively or via Finset.card, and prove the recurrence on that function.

- [ ] **Step 4: Build and commit**

Run: `lake build LeanModularForms.Modularforms.Generators`

```bash
git add LeanModularForms/Modularforms/Generators.lean
git commit -m "feat(Generators): combinatorial helpers for monomial weight counting"
```

---

### Task 4: Q-expansion and Delta Helpers

**Files:**
- Modify: `LeanModularForms/Modularforms/Generators.lean`

- [ ] **Step 1: Constant q-coeff of E₄^a * E₆^b is 1**

```lean
/-- The 0th q-expansion coefficient of E₄^a * E₆^b is 1 (for a + b > 0). -/
lemma E₄_pow_E₆_pow_qexp_zero (a b : ℕ) (hab : 0 < a + b) :
    (qExpansion 1 (↑(ModularForm.mul_pow_E₄_E₆ a b))).coeff 0 = 1 := by
  sorry
```

where `ModularForm.mul_pow_E₄_E₆ a b` is a helper for the product. If this auxiliary is awkward, work directly with the product of modular forms in the DirectSum.

**Alternative formulation** (likely easier to work with):

```lean
/-- The q-expansion of the product E₄^a * E₆^b has constant coefficient 1. -/
lemma qexp_coeff_zero_E₄_pow_mul_E₆_pow (a b : ℕ) (hab : 0 < a + b) :
    (qExpansion 1 (((DirectSum.of _ 4 E₄) ^ a * (DirectSum.of _ 6 E₆) ^ b :
      ⨁ k : ℤ, ModularForm Γ(1) k) (↑(4 * a + 6 * b)))).coeff 0 = 1 := by
  sorry
```

**Proof strategy:** By induction on `a + b`. Base cases `(1,0)` and `(0,1)` use `E4_q_exp_zero` and `E6_q_exp_zero`. Inductive step uses `qExpansion_mul_coeff` with the Cauchy product formula: `coeff 0 (f * g) = coeff 0 f * coeff 0 g`, then the inductive hypothesis gives both factors have constant coeff 1.

The key existing lemma is:
```
qExpansion_mul_coeff : ... (qExpansion n (f.mul g)) = (qExpansion n f) * (qExpansion n g)
```
(in `qExpansion_lems.lean:118`). After rewriting with this, `PowerSeries.coeff_mul` gives `coeff 0 (p * q) = coeff 0 p * coeff 0 q` (via `Finset.antidiagonal_zero`).

- [ ] **Step 2: Delta equals evalE₄E₆ of Delta_poly**

```lean
/-- Delta is the image of Delta_poly under evalE₄E₆ at weight 12. -/
lemma evalE₄E₆_Delta_poly :
    (evalE₄E₆ Delta_poly) 12 = ModularForm.mcast (by norm_num : (12 : ℤ) = 12)
      (ModForm_mk Γ(1) 12 Delta) := by
  sorry
```

**Alternative (simpler statement):**

```lean
/-- Delta, viewed in the graded ring, is in the range of evalE₄E₆. -/
lemma delta_mem_range_evalE₄E₆ :
    DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) 12
      (ModForm_mk Γ(1) 12 Delta) ∈ Set.range evalE₄E₆ := by
  sorry
```

**Proof strategy:** Unfold `evalE₄E₆` and `Delta_poly`. Show:
```
evalE₄E₆ Delta_poly
  = (1/1728) • ((DirectSum.of _ 4 E₄)^3 - (DirectSum.of _ 6 E₆)^2)
```
Then use `Delta_E4_eqn : Delta = Delta_E4_E6_aux` and `Delta_E4_E6_eq` which shows `ModForm_mk _ _ Delta_E4_E6_aux = (1/1728) • ((DirectSum.of _ 4 E₄)^3 - (DirectSum.of _ 6 E₆)^2) 12`.

The witness polynomial is `Delta_poly = (1/1728) • (X 0 ^ 3 - X 1 ^ 2)`.

Use `MvPolynomial.aeval_X`, `map_pow`, `map_sub`, `map_smul` to simplify `evalE₄E₆ Delta_poly`.

- [ ] **Step 3: Build and commit**

Run: `lake build LeanModularForms.Modularforms.Generators`

```bash
git add LeanModularForms/Modularforms/Generators.lean
git commit -m "feat(Generators): q-expansion helpers and Delta in evalE₄E₆ range"
```

---

### Task 5: Surjectivity

**Files:**
- Modify: `LeanModularForms/Modularforms/Generators.lean`

- [ ] **Step 1: State surjectivity on DirectSum.of components**

It suffices to show that for each k and each `f : ModularForm Γ(1) k`, the element `DirectSum.of _ k f` is in the range of `evalE₄E₆`. Since elements of the DirectSum are finite sums of such components, and the range is a subalgebra (hence a subgroup), this gives full surjectivity.

```lean
/-- Every modular form of weight k is in the image of evalE₄E₆. -/
lemma evalE₄E₆_surjective_weight (k : ℤ) (f : ModularForm Γ(1) k) :
    DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) k f ∈ Set.range evalE₄E₆ := by
  sorry
```

- [ ] **Step 2: Prove base cases**

Handle the cases where the proof doesn't require induction. These should be separate lemmas called from the main proof:

```lean
/-- Weight 0: constants are in the image (via constant polynomials). -/
private lemma surj_weight_zero (f : ModularForm Γ(1) 0) :
    DirectSum.of _ (0 : ℤ) f ∈ Set.range evalE₄E₆ := by
  sorry -- f = c * 1, and evalE₄E₆ (MvPolynomial.C c) = DirectSum.of _ 0 (c • 1)

/-- Negative weights: M_k = 0. -/
private lemma surj_neg_weight {k : ℤ} (hk : k < 0) (f : ModularForm Γ(1) k) :
    DirectSum.of _ k f ∈ Set.range evalE₄E₆ := by
  sorry -- f = 0 by levelOne_neg_weight_eq_zero, DirectSum.of _ k 0 = 0 = evalE₄E₆ 0

/-- Odd weights: M_k = 0. -/
private lemma surj_odd_weight {k : ℤ} (hk : Odd k) (f : ModularForm Γ(1) k) :
    DirectSum.of _ k f ∈ Set.range evalE₄E₆ := by
  sorry -- f = 0 by levelOne_odd_weight_eq_zero

/-- Weight 2: M_2 = 0. -/
private lemma surj_weight_two (f : ModularForm Γ(1) 2) :
    DirectSum.of _ (2 : ℤ) f ∈ Set.range evalE₄E₆ := by
  sorry -- f = 0 by weight_two_zero
```

**Proof strategy for each:**
- Negative/odd/weight-2: show `f = 0` using the relevant vanishing lemma, then `DirectSum.of _ k 0 = 0 = evalE₄E₆ 0`.
- Weight 0: `f` is a constant `c • 1` by `levelOne_weight_zero_const`. Then `evalE₄E₆ (MvPolynomial.C c)` should equal `DirectSum.of _ 0 (c • 1)` by `MvPolynomial.aeval_C`.

- [ ] **Step 3: Prove base cases for weights 4, 6, 8, 10**

```lean
/-- Weight 4: M_4 = C * E₄, which is the image of c * X₀. -/
private lemma surj_weight_four (f : ModularForm Γ(1) 4) :
    DirectSum.of _ (4 : ℤ) f ∈ Set.range evalE₄E₆ := by
  sorry
```

**Proof strategy:** Use `exists_smul_eq_of_rank_one weight_four_one_dimensional E4_ne_zero f` to get `f = c • E₄`. Then `evalE₄E₆ (MvPolynomial.C c * MvPolynomial.X 0) = c • DirectSum.of _ 4 E₄ = DirectSum.of _ 4 f`. Use `MvPolynomial.aeval_X` and `MvPolynomial.aeval_C`.

Similarly for weights 6 (`c • E₆`, polynomial `c * X₁`), 8 (`c • E₄²`, polynomial `c * X₀²`), 10 (`c • E₄*E₆`, polynomial `c * X₀ * X₁`).

For weights 8 and 10, use `weight_eight_one_dimensional` (which handles all even k with 3 ≤ k and k < 12) to get `f = c • E k hk`. Then express E(8) as E₄² and E(10) as E₄*E₆ via the 1-dimensionality (E₄² ∈ M_8, E₄*E₆ ∈ M_10, and each space is 1-dimensional).

- [ ] **Step 4: Prove the inductive step (k >= 12 even)**

```lean
/-- Inductive step: for even k >= 12, surjectivity at k follows from k-12. -/
private lemma surj_inductive_step (k : ℤ) (hk : 12 ≤ k) (hkeven : Even k)
    (ih : ∀ j : ℤ, j < k → ∀ g : ModularForm Γ(1) j,
      DirectSum.of _ j g ∈ Set.range evalE₄E₆)
    (f : ModularForm Γ(1) k) :
    DirectSum.of _ k f ∈ Set.range evalE₄E₆ := by
  sorry
```

**Proof strategy (the core argument):**
1. Use `monomial_weight_exists` to get `a, b` with `4*a + 6*b = k` (cast to ℕ; k ≥ 12 and even so k.toNat ≥ 12).
2. Let `c := (qExpansion 1 f).coeff 0`.
3. Let `m := E₄^a * E₆^b` (as a modular form of weight k, constructed via the graded product).
4. Let `g := f - c • m : ModularForm Γ(1) k`.
5. Show `(qExpansion 1 g).coeff 0 = 0` using:
   - `(qExpansion 1 f).coeff 0 = c` (by definition)
   - `(qExpansion 1 m).coeff 0 = 1` (from `qexp_coeff_zero_E₄_pow_mul_E₆_pow`)
   - Linearity of qExpansion
6. By `IsCuspForm_iff_coeffZero_eq_zero`, g is a cusp form.
7. Using `IsCuspForm_to_CuspForm`, get `g' : CuspForm Γ(1) k` with `g' = g`.
8. Apply `CuspForms_iso_Modforms k` to get `h := (CuspForms_iso_Modforms k) g' : ModularForm Γ(1) (k-12)`.
9. By the inductive hypothesis (with `j = k - 12 < k`), `h` is in the range: `∃ p_h, evalE₄E₆ p_h = DirectSum.of _ (k-12) h`.
10. Since Delta is in the range (`delta_mem_range_evalE₄E₆`): `∃ p_Δ, evalE₄E₆ p_Δ = DirectSum.of _ 12 Delta`.
11. Then `g = Delta * h` in the graded ring (by construction of `CuspForms_iso_Modforms`), so `g = evalE₄E₆ (p_Δ * p_h)`.
12. And `c • m = evalE₄E₆ (MvPolynomial.C c * X 0 ^ a * X 1 ^ b)`.
13. So `f = g + c • m = evalE₄E₆ (p_Δ * p_h + MvPolynomial.C c * X 0 ^ a * X 1 ^ b)`.

The trickiest part is step 11: showing that multiplication in the DirectSum corresponds to `Modform_mul_Delta'`. The key identity is:
```
DirectSum.of _ 12 Delta * DirectSum.of _ (k-12) h = DirectSum.of _ k (mul_Delta_map k h)
```
using `GradedMonoid.GMul.mul` and `ModularForm.mul`. This needs `12 + (k-12) = k` (omega).

- [ ] **Step 5: Assemble the full surjectivity proof**

```lean
theorem evalE₄E₆_surjective : Function.Surjective evalE₄E₆ := by
  sorry
```

**Proof strategy:** Use `DirectSum.surjective_of_surjective_on_of` or show the range contains all `DirectSum.of _ k f` (which span the DirectSum). Then apply strong induction on k via `Int.strong_induction_on` or well-founded recursion. Dispatch to base cases and inductive step.

Specifically: to show every element of `⨁ k, M_k` is in the range, it suffices to show every `DirectSum.of _ k f` is, because the range is a subalgebra. Then use `evalE₄E₆_surjective_weight` (which dispatches to the base cases and inductive step based on k).

Alternatively, use `AlgHom.range_eq_top_iff` and `Algebra.adjoin_eq_top_iff` if that's cleaner.

- [ ] **Step 6: Build and commit**

Run: `lake build LeanModularForms.Modularforms.Generators`

```bash
git add LeanModularForms/Modularforms/Generators.lean
git commit -m "feat(Generators): surjectivity of evalE₄E₆"
```

---

### Task 6: Injectivity via Dimension Counting

**Files:**
- Modify: `LeanModularForms/Modularforms/Generators.lean`

- [ ] **Step 1: Finite-dimensionality of M_k for level 1**

```lean
/-- Modular forms of any weight for Gamma(1) are finite-dimensional. -/
instance finiteDimensional_modform_levelOne (k : ℤ) :
    FiniteDimensional ℂ (ModularForm Γ(1) k) := by
  sorry
```

**Proof strategy:** Case split:
- k < 0: `M_k = 0` (rank 0 → finite-dimensional of dim 0)
- k odd: `M_k = 0` (from Task 2)
- k = 0: rank 1 (from `levelOne_weight_zero_rank_one`)
- k = 2: rank 0 (from `dim_weight_two`)
- k even, k ≥ 4: use `dim_modforms_lvl_one` which gives an explicit ℕ value for `Module.rank`; a module whose rank is a natural number is finite-dimensional.

Use `Module.finite_of_rank_eq_nat` or similar to convert `Module.rank = ↑n` into `FiniteDimensional`.

- [ ] **Step 2: evalE₄E₆ respects grading**

```lean
/-- evalE₄E₆ maps weighted-homogeneous polynomials of degree n to weight-n forms. -/
lemma evalE₄E₆_grading (p : MvPolynomial (Fin 2) ℂ)
    (n : ℕ) (hp : MvPolynomial.IsWeightedHomogeneous (fun i : Fin 2 => (E₄E₆Weight i : ℤ)) p (n : ℤ)) :
    ∀ k : ℤ, k ≠ ↑n → (evalE₄E₆ p) k = 0 := by
  sorry
```

**Proof strategy:** By induction on the structure of weighted-homogeneous polynomials (monomials, sums, scalar multiples). For a monomial `X 0 ^ a * X 1 ^ b` with `4a + 6b = n`, `evalE₄E₆` maps it to `(DirectSum.of _ 4 E₄)^a * (DirectSum.of _ 6 E₆)^b`, which by graded multiplication lives entirely in weight `4a + 6b = n`.

This may be provable more directly using the general fact that `aeval` of a weighted-homogeneous polynomial into a graded algebra lands in the correct graded piece. Check if mathlib has `GradedAlgebra.aeval_isWeightedHomogeneous` or similar.

- [ ] **Step 3: Dimension of weighted-homogeneous piece equals dim M_k**

```lean
/-- The monomial count and modular forms dimension satisfy the same recurrence
    with the same base cases, hence are equal. -/
lemma dim_weightedHomogeneous_eq_rank (k : ℕ) (hkeven : Even k) :
    Module.rank ℂ (MvPolynomial.weightedHomogeneousSubmodule ℂ
      (fun i : Fin 2 => (E₄E₆Weight i : ℤ)) (k : ℤ)) =
    Module.rank ℂ (ModularForm Γ(1) (k : ℤ)) := by
  sorry
```

**Proof strategy:** Both sides satisfy:
- `d(k) = 0` for k odd (poly side: no monomials; forms side: Task 2)
- `d(k) = 0` for k < 0 (poly side: trivially; forms side: `levelOne_neg_weight_rank_zero`)
- `d(0) = 1, d(2) = 0, d(4) = d(6) = d(8) = d(10) = 1` (verify directly for poly side)
- `d(k) = 1 + d(k-12)` for k ≥ 12 even (poly side: `monomial_count_step`; forms side: `dim_modforms_eq_one_add_dim_cuspforms` + `CuspForms_iso_Modforms`)

Prove by strong induction on k. Base cases k < 12 by direct computation. Inductive step by the recurrence.

The rank of `weightedHomogeneousSubmodule` for the polynomial side may be easier to work with as `Module.finrank` (since it's finite-dimensional). The monomial set `{X 0^a * X 1^b : 4a+6b = k}` is a basis for this submodule; its cardinality is the count from Task 3.

Alternatively, if working with `Module.rank` (cardinals) is awkward, work with `Module.finrank` (ℕ) throughout and convert at the end.

- [ ] **Step 4: Prove injectivity**

```lean
theorem evalE₄E₆_injective : Function.Injective evalE₄E₆ := by
  sorry
```

**Proof strategy:** If `evalE₄E₆ p = 0`, decompose `p` into weighted-homogeneous components `p = ∑ pₙ` using `MvPolynomial.sum_weightedHomogeneousComponent`. Since `evalE₄E₆` respects grading (Step 2), each `evalE₄E₆ pₙ = 0`. The restricted map on each weight-n subspace is surjective (from Task 5) and source/target have the same finite dimension (Step 3). A surjective linear map between finite-dimensional spaces of equal dimension is injective. So `pₙ = 0` for all n, hence `p = 0`.

Use `LinearMap.injective_of_surjective_of_finrank_eq` or the equivalent: for f.d. vector spaces of the same dimension, surjective ↔ injective.

- [ ] **Step 5: Build and commit**

Run: `lake build LeanModularForms.Modularforms.Generators`

```bash
git add LeanModularForms/Modularforms/Generators.lean
git commit -m "feat(Generators): injectivity of evalE₄E₆ via dimension counting"
```

---

### Task 7: Main Isomorphism and Corollary

**Files:**
- Modify: `LeanModularForms/Modularforms/Generators.lean`

- [ ] **Step 1: Construct the algebra isomorphism**

```lean
/-- The graded ring of level 1 modular forms is isomorphic to the weighted polynomial
    ring in E₄ (weight 4) and E₆ (weight 6). -/
noncomputable def modularFormsEquivMvPolynomial :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] ⨁ k : ℤ, ModularForm Γ(1) k :=
  AlgEquiv.ofBijective evalE₄E₆ ⟨evalE₄E₆_injective, evalE₄E₆_surjective⟩
```

This should be definitional given Tasks 5 and 6.

- [ ] **Step 2: Per-weight spanning corollary**

```lean
/-- Every modular form of weight k for Gamma(1) is a C-linear combination of
    monomials E₄^a * E₆^b with 4a + 6b = k. -/
theorem modularForm_in_E₄E₆_span (k : ℤ) (f : ModularForm Γ(1) k) :
    ∃ p : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.IsWeightedHomogeneous (fun i : Fin 2 => (E₄E₆Weight i : ℤ)) p k ∧
      (evalE₄E₆ p) k = f := by
  sorry
```

**Proof strategy:** Since `evalE₄E₆` is surjective, `DirectSum.of _ k f` has a preimage `p`. Decompose `p` into weighted-homogeneous components. The k-component of `evalE₄E₆ p` equals `f`, and by grading only the weight-k component of `p` contributes. So take `p_k = weightedHomogeneousComponent k p`.

- [ ] **Step 3: Algebra.adjoin characterization**

```lean
/-- E₄ and E₆ generate the entire graded ring of level 1 modular forms. -/
theorem E₄E₆_generate :
    Algebra.adjoin ℂ ({DirectSum.of _ 4 E₄, DirectSum.of _ 6 E₆} :
      Set (⨁ k : ℤ, ModularForm Γ(1) k)) = ⊤ := by
  sorry
```

**Proof strategy:** Since `evalE₄E₆ = MvPolynomial.aeval ![e₄, e₆]` is surjective, the range of `aeval` is `⊤`. And `MvPolynomial.aeval_range` states that the range of `aeval` equals `Algebra.adjoin` of the image elements.

Use `MvPolynomial.aeval_range` (or `MvPolynomial.range_aeval_eq_adjoin` depending on mathlib version).

- [ ] **Step 4: Build and commit**

Run: `lake build LeanModularForms.Modularforms.Generators`

```bash
git add LeanModularForms/Modularforms/Generators.lean
git commit -m "feat(Generators): graded ring isomorphism MvPolynomial ≃ₐ ⨁ M_k(Gamma(1))"
```

---

## Notes for the Implementing Agent

### Key Existing API Reference

| Lemma | File | Signature |
|-------|------|-----------|
| `IsCuspForm_iff_coeffZero_eq_zero` | IsCuspForm.lean:161 | `IsCuspForm Γ(1) k f ↔ (qExpansion 1 f).coeff 0 = 0` |
| `CuspForms_iso_Modforms` | DimensionFormulas.lean:76 | `CuspForm Γ(1) k ≃ₗ[ℂ] ModularForm Γ(1) (k - 12)` |
| `IsCuspForm_weight_lt_eq_zero` | DimensionFormulas.lean:119 | `k < 12 → IsCuspForm → f = 0` |
| `cuspform_weight_lt_12_zero` | DimensionFormulas.lean:112 | `k < 12 → rank (CuspForm Γ(1) k) = 0` |
| `dim_modforms_eq_one_add_dim_cuspforms` | DimensionFormulas.lean:432 | `rank M_k = 1 + rank S_k` (k even, k ≥ 4) |
| `weight_four_one_dimensional` | DimensionFormulas.lean:242 | `rank M_4 = 1` |
| `weight_six_one_dimensional` | DimensionFormulas.lean:204 | `rank M_6 = 1` |
| `weight_eight_one_dimensional` | DimensionFormulas.lean:279 | `rank M_k = 1` for even k with 3 ≤ k < 12 |
| `Delta_E4_eqn` | DimensionFormulas.lean:185 | `Delta = Delta_E4_E6_aux` |
| `Delta_E4_E6_eq` | DimensionFormulas.lean:134 | `ModForm_mk _ _ Delta_E4_E6_aux = (1/1728) • (E₄³ - E₆²) 12` |
| `E4_q_exp_zero` | Eisenstein.lean:517 | `(qExpansion 1 E₄).coeff 0 = 1` |
| `E6_q_exp_zero` | Eisenstein.lean:561 | `(qExpansion 1 E₆).coeff 0 = 1` |
| `exists_smul_eq_of_rank_one` | Eisenstein.lean:21 | `rank = 1 → e ≠ 0 → ∃ c, f = c • e` |
| `levelOne_neg_weight_rank_zero` | mathlib LevelOne.lean:100 | `k < 0 → rank M_k = 0` |
| `levelOne_weight_zero_rank_one` | mathlib LevelOne.lean:95 | `rank M_0 = 1` |
| `dim_weight_two` | DimensionFormulas.lean:469 | `rank M_2 = 0` |
| `qExpansion_mul_coeff` | qExpansion_lems.lean:118 | q-expansion of product = product of q-expansions |

### MvPolynomial API Reference

| Lemma/Def | Purpose |
|-----------|---------|
| `MvPolynomial.aeval` | Algebra hom from `MvPolynomial σ R` to any R-algebra |
| `MvPolynomial.aeval_X` | `aeval f (X i) = f i` |
| `MvPolynomial.aeval_C` | `aeval f (C r) = algebraMap R A r` |
| `MvPolynomial.IsWeightedHomogeneous` | Predicate for weighted homogeneity |
| `MvPolynomial.weightedHomogeneousSubmodule` | Submodule of weight-n polys |
| `MvPolynomial.weightedHomogeneousComponent` | Projection to weight-n component |
| `MvPolynomial.sum_weightedHomogeneousComponent` | Decomposition into components |
| `MvPolynomial.weightedGradedAlgebra` | GradedAlgebra instance |

### Common Patterns in This Codebase

- q-expansion manipulations require `← Nat.cast_one (R := ℝ)` before using `qExpansion_sub`, `qExpansion_smul2`
- DirectSum elements: `DirectSum.of (fun k : ℤ => ModularForm Γ(1) k) k f` lifts `f` into the graded ring
- Graded multiplication: `(DirectSum.of _ k₁ f) * (DirectSum.of _ k₂ g)` gives weight `k₁ + k₂`
- Level 1 notation: `Γ(1)` expands to `CongruenceSubgroup.Gamma 1` (or `CongruenceSubgroup.Gamma ↑1`)
- Use `ModularForm.mcast` for weight-casting: if `h : k₁ = k₂`, then `mcast h f` recasts the weight

### Potential Difficulties

1. **ℕ/ℤ coercion:** Polynomial weights are natural (`E₄E₆Weight : Fin 2 → ℕ`) but modular form weights are integers. Cast with `(↑n : ℤ)` and use `Nat.cast_*` lemmas.

2. **DirectSum algebra instance:** The `Algebra ℂ (⨁ k, ModularForm Γ(1) k)` instance requires `(CongruenceSubgroup.Gamma 1).HasDetOne` or similar. Check that this resolves; you may need `haveI` for local instances.

3. **Graded multiplication in DirectSum:** Showing `(DirectSum.of _ 4 E₄)^a` equals `DirectSum.of _ (4*a) (E₄^a)` requires unwinding `GradedMonoid.GMul` definitions. This may need induction on `a` with `DirectSum.of_mul_of` or similar.

4. **Injectivity argument:** The decomposition of `p` into weighted-homogeneous components and the per-weight injectivity argument requires carefully combining `sum_weightedHomogeneousComponent` with the grading property.
