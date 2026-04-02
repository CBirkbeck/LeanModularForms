# E4-E6 Generators: Graded Ring Isomorphism

## Goal

Prove that the graded ring of level 1 modular forms is isomorphic to the weighted polynomial ring in E4 and E6:

```
MvPolynomial (Fin 2) ℂ  ≃ₐ[ℂ]  ⨁ k : ℤ, ModularForm Γ(1) k
```

with weight function `![4, 6]` (X₀ has weight 4, X₁ has weight 6).

As a corollary, derive per-weight spanning: every f ∈ M_k(Γ(1)) is a ℂ-linear combination of monomials E₄^a · E₆^b with 4a + 6b = k.

## File

`LeanModularForms/Modularforms/Generators.lean` (new file)

## Imports

- `Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous`
- `Mathlib.RingTheory.MvPolynomial.Basic`
- Project: `Eisenstein`, `DimensionFormulas`, `Delta`, `IsCuspForm`

## Core Definitions

### Weight function

```lean
def E₄E₆Weight : Fin 2 → ℕ := ![4, 6]
```

### Evaluation homomorphism

```lean
noncomputable def evalE₄E₆ :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ⨁ k : ℤ, ModularForm Γ(1) k :=
  MvPolynomial.aeval ![DirectSum.of _ 4 E₄, DirectSum.of _ 6 E₆]
```

### Main result

```lean
noncomputable def modularFormsEquivMvPolynomial :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] ⨁ k : ℤ, ModularForm Γ(1) k :=
  AlgEquiv.ofBijective evalE₄E₆ ⟨evalE₄E₆_injective, evalE₄E₆_surjective⟩
```

## Proof Strategy

### Surjectivity (strong induction on weight k)

For each k, show `DirectSum.of _ k f ∈ Set.range evalE₄E₆` for all `f : ModularForm Γ(1) k`.

**Base cases:**
- k odd, k < 0, k = 2: M_k = 0, trivial
- k = 0: constants, image of constant polynomials
- k = 4: M_4 = ℂ·E₄ (`weight_four_one_dimensional`), image of X₀
- k = 6: M_6 = ℂ·E₆ (`weight_six_one_dimensional`), image of X₁
- k = 8: M_8 = ℂ·E₄² (`weight_eight_one_dimensional`), image of X₀²
- k = 10: 1-dimensional, spanned by E₄·E₆, image of X₀·X₁

**Inductive step (k ≥ 12 even):**
1. Pick (a, b) with 4a + 6b = k (always exists for even k ≥ 4, `monomial_exists`)
2. Let c = (qExpansion 1 f).coeff 0 (constant q-coefficient of f)
3. Form g = f - c • E₄^a · E₆^b
4. g has 0th q-coeff = 0 because E₄^a·E₆^b has constant q-coeff 1 (`E₄_pow_E₆_pow_qexp_zero`)
5. By `IsCuspForm_iff_coeffZero_eq_zero`, g is a cusp form
6. By `CuspForms_iso_Modforms`, g = Δ · h for some h ∈ M_{k-12}
7. By induction, h is in the image of evalE₄E₆
8. Δ = (E₄³ - E₆²)/1728 is in the image (`delta_mem_range_evalE₄E₆`)
9. So g = Δ · h is in the image, hence f = c • E₄^a·E₆^b + g is in the image

### Injectivity (dimension counting)

Both sides have the same dimension in each graded piece, proved by parallel recurrence:

**Polynomial side:** #{(a,b) ∈ ℕ² : 4a + 6b = k} satisfies:
- d(k) = 1 + d(k - 12) for k ≥ 12 even
- Proof: bijection (a,b) ↦ (a+3,b) from {4a+6b = k-12} to {4a+6b = k, a ≥ 3}, plus exactly one solution with a < 3 for even k ≥ 4

**Modular forms side:** dim M_k satisfies:
- dim M_k = 1 + dim M_{k-12} for k ≥ 12 even
- From `dim_modforms_eq_one_add_dim_cuspforms` + `CuspForms_iso_Modforms`

**Base cases (k < 12) match:** verified directly for k = 0,2,4,6,8,10 (and odd/negative).

**Conclusion:** Surjective linear map between finite-dimensional spaces of equal dimension is injective.

## Helper Lemmas

### Combinatorial

1. `monomial_exists (k : ℕ) (hk : Even k) (hk4 : 4 ≤ k) : ∃ a b : ℕ, 4 * a + 6 * b = k`
2. `monomial_count_recurrence (k : ℕ) (hk : 12 ≤ k) (hkeven : Even k) :` the count at k = 1 + count at k-12

### Q-expansion

3. `E₄_pow_E₆_pow_qexp_zero (a b : ℕ) : (qExpansion 1 (E₄ ^ a * E₆ ^ b)).coeff 0 = 1`
   Uses existing `E4_q_exp_zero`, `E6_q_exp_zero`, and multiplicativity of q-expansion.

### Structural

4. `delta_mem_range_evalE₄E₆ : DirectSum.of _ 12 Δ ∈ Set.range evalE₄E₆`
   From `delta_eq_E4E6_const`: Δ = (E₄³ - E₆²)/1728 = evalE₄E₆ ((X₀³ - X₁²)/1728)

5. `finiteDimensional_modform_levelOne (k : ℤ) : FiniteDimensional ℂ (ModularForm Γ(1) k)`
   Follows from the dimension formula giving finite cardinal values.

6. `dim_eq_monomial_count (k : ℕ) (hkeven : Even k) : Module.rank ℂ (ModularForm Γ(1) k) = #{4a+6b=k}`
   By the parallel recurrence argument.

### Existing results used

- `IsCuspForm_iff_coeffZero_eq_zero` (IsCuspForm.lean:161) — cusp ↔ 0th coeff = 0
- `CuspForms_iso_Modforms` (DimensionFormulas.lean) — S_k ≅ M_{k-12} via Δ
- `cuspform_weight_lt_12_zero` (DimensionFormulas.lean) — no cusp forms for k < 12
- `weight_four_one_dimensional` (DimensionFormulas.lean) — dim M_4 = 1
- `weight_six_one_dimensional` (DimensionFormulas.lean) — dim M_6 = 1
- `weight_eight_one_dimensional` (DimensionFormulas.lean) — dim M_8 = 1
- `dim_modforms_eq_one_add_dim_cuspforms` (DimensionFormulas.lean) — dim M_k = 1 + dim S_k
- `delta_eq_E4E6_const` (DimensionFormulas.lean) — Δ = c·(E₄³ - E₆²)
- `E4_q_exp_zero`, `E6_q_exp_zero` (Eisenstein.lean) — constant q-coefficients = 1
- `E₄`, `E₆` definitions (Eisenstein.lean)

## Corollary

```lean
theorem modularForm_span_E₄E₆ (k : ℤ) (f : ModularForm Γ(1) k) :
    ∃ p : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.IsWeightedHomogeneous E₄E₆Weight p k ∧
      evalE₄E₆ p = DirectSum.of _ k f
```

This is option 1 (per-weight spanning) derived from the graded isomorphism.
